/-
  EvmAsm.Rv64.RLP.ContentToU64

  A verified RISC-V leaf subroutine that is a **canonical-strict drop-in
  replacement** for the codegen guest function `rlp_content_to_u64` emitted by
  `EvmAsm/Codegen/Programs/RlpWalk.lean` (`rlpContentToU64Function`, added in
  #9503's cursor-walk RLP decode work).

  The guest routine decodes the prefix-stripped payload of an RLP byte-string
  item (an Ethereum *scalar* that fits in 64 bits — a `u64` nonce / gas / chain
  id, etc.) into a register, big-endian. This verified version additionally
  enforces the RLP **scalar canonicality** rule (execution-specs
  `_deserialize_to_uint`, mirrored by the now-strict `EvmAsm.EL.RLP.decodeScalar`):
  the empty string is the canonical `0`, but a nonzero value's high byte must be
  nonzero — a `len > 0` content with `content[0] = 0` is **non-canonical** and
  rejected. (The current guest is lenient; this is a corrected drop-in.)

  ## Caller-facing contract (LP64)

  Frameless leaf: reached by `jal ra, rlp_content_to_u64`, returns via `ret`.

  ### Inputs
  * `a0` (`x10`) — pointer to the `content` bytes (prefix-stripped payload).
  * `a1` (`x11`) — `content` byte length.

  ### Outputs
  * `a0` (`x10`) — the decoded `u64` value (big-endian) on the success paths; `0`
    on every failure path.
  * `a1` (`x11`) — **status**: `0` ok / `2` too long (`len > 8`) / `3`
    non-canonical (`len > 0 ∧ content[0] = 0`).

  Scratch `t0..t3` (`x5`,`x6`,`x7`,`x28`) are clobbered; `ra` preserved. Unlike
  `rlp_content_to_u256_be`, there is **no output memory region** — the result is
  returned in `a0`.

  ## Verification status

  Lays out the 22-instruction canonical-strict body `rlp_content_to_u64_prog`.
  Proved: the **too-long failure path** (`len > 8`, status 2). Follow-ups (this
  is a stacked-PR sequence): the non-canonical path (status 3), the big-endian
  accumulation loop (`a0 = fromBytesBE content`), the empty (`len = 0`) and
  success (`0 < len ≤ 8 ∧ content[0] ≠ 0`) paths, and the unified disjunctive
  theorem (per the `AGENTS.md` spec-design convention).
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
import EvmAsm.EL.RLP.Scalar

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
The verified **canonical-strict** drop-in body for the codegen guest
`rlp_content_to_u64` (22 instructions). Register map: `a0=x10`, `a1=x11`,
`t0=x5`, `t1=x6`, `t2=x7`, `t3=x28`, `ra=x1`.

```
   0  LI   x5  8         ; t0 = 8
   1  BLTU x5  x11 72    ; if 8 < len goto too_long (idx 19, +72)
   2  MV   x6  x10       ; t1 = ptr
   3  MV   x7  x11       ; t2 = remaining
   4  LI   x10 0         ; a0 = 0 (accumulator / value)
   5  BEQ  x7  x0  40    ; if len == 0 goto done (canonical 0; idx 15, +40)
   6  LBU  x28 x6  0     ; t3 = content[0] (high byte)
   7  BEQ  x28 x0  40    ; if high byte == 0 goto noncanon (idx 17, +40)
   8  BEQ  x7  x0  28    ; loop head: if remaining == 0 goto done (idx 15, +28)
   9  SLLI x10 x10 8     ; a0 <<= 8
  10  LBU  x28 x6  0     ; t3 = content[k]
  11  OR   x10 x10 x28   ; a0 |= t3
  12  ADDI x6  x6  1
  13  ADDI x7  x7  (-1)
  14  JAL  x0  (-24)     ; goto loop head (idx 8)
  15  LI   x11 0         ; done: a1 = 0 (ok)
  16  JALR x0  x1  0     ; ret
  17  LI   x11 3         ; noncanon: a1 = 3   (a0 already 0)
  18  JALR x0  x1  0     ; ret
  19  LI   x10 0         ; too_long: a0 = 0
  20  LI   x11 2         ; a1 = 2
  21  JALR x0  x1  0     ; ret
```
-/
def rlp_content_to_u64_prog : List Instr :=
  [ .LI .x5 (8 : Word),              -- 0
    .BLTU .x5 .x11 (72 : BitVec 13), -- 1
    .MV .x6 .x10,                    -- 2
    .MV .x7 .x11,                    -- 3
    .LI .x10 (0 : Word),             -- 4
    .BEQ .x7 .x0 (40 : BitVec 13),   -- 5
    .LBU .x28 .x6 0,                 -- 6
    .BEQ .x28 .x0 (40 : BitVec 13),  -- 7
    .BEQ .x7 .x0 (28 : BitVec 13),   -- 8
    .SLLI .x10 .x10 (8 : BitVec 6),  -- 9
    .LBU .x28 .x6 0,                 -- 10
    .OR .x10 .x10 .x28,              -- 11
    .ADDI .x6 .x6 (1 : BitVec 12),   -- 12
    .ADDI .x7 .x7 (-1 : BitVec 12),  -- 13
    .JAL .x0 (-24 : BitVec 21),      -- 14
    .LI .x11 (0 : Word),             -- 15
    .JALR .x0 .x1 0,                 -- 16
    .LI .x11 (3 : Word),             -- 17
    .JALR .x0 .x1 0,                 -- 18
    .LI .x10 (0 : Word),             -- 19
    .LI .x11 (2 : Word),             -- 20
    .JALR .x0 .x1 0 ]                -- 21

theorem rlp_content_to_u64_prog_length :
    rlp_content_to_u64_prog.length = 22 := rfl

/-- The drop-in body as a `CodeReq` rooted at `base`. -/
abbrev rlp_content_to_u64_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_content_to_u64_prog

/--
**`rlp_content_to_u64` — content-too-long failure path.**

When the content length exceeds 8 bytes (`8 <ᵤ len`, cannot fit a `u64`), the
routine returns value `a0 = 0` and status `a1 = 2`. `ra` is preserved; `t0`
(`x5`) is clobbered to `8`. No memory is touched. The routine returns to
`ra &&& ~~~1`.
-/
theorem rlp_content_to_u64_too_long_spec_within
    (base contentPtr len t0Old raVal : Word)
    (h_too_long : BitVec.ult (8 : Word) len) :
    cpsTripleWithin 5 base (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ t0Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  -- Phase A: LI x5 8 (idx 0), base → base + 4.
  have hLI := li_spec_gen_within .x5 t0Old (8 : Word) base (by decide)
  -- Phase B: BLTU x5 x11 72 at base+4, taken since 8 <ᵤ len (idx 1), base+4 → base+76.
  have hbltu := bltu_spec_gen_within .x5 .x11 (72 : BitVec 13) (8 : Word) len (base + 4)
  have ha_t : (base + 4) + signExtend13 (72 : BitVec 13) = base + 76 := by
    rw [show signExtend13 (72 : BitVec 13) = (72 : Word) from by decide]; bv_omega
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_omega
  rw [ha_t, ha_f] at hbltu
  have hmono1 : ∀ a i, CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (72 : BitVec 13)) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 1 (base + 4)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hB := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono1 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ contentPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_too_long)
  -- Phase C: LI x10 0 ; LI x11 2 ; ret  (idx 19, 20, 21), base+76 → ra &&& ~~~1.
  have hLI0 := li_spec_gen_within .x10 contentPtr (0 : Word) (base + 76) (by decide)
  have hLI2 := li_spec_gen_within .x11 len (2 : Word) (base + 80) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 84)
  simp only [signExtend12_0] at hRet
  have hC : cpsTripleWithin 3 (base + 76) (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ len) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** ⌜BitVec.ult (8 : Word) len⌝)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** ⌜BitVec.ult (8 : Word) len⌝) := by
    runBlock hLI0 hLI2 hRet
  -- Phase A as a triple over the full code (idx 0), base → base+4.
  have hA : cpsTripleWithin 1 base (base + 4) (rlp_content_to_u64_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal))
      ((.x5 ↦ᵣ (8 : Word)) ** (.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ len) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal)) := by
    runBlock hLI
  -- Compose A ⨾ B(taken) ⨾ C.
  have hAB := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB
  have hFull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hAB hC
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hp => sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)))) h hp) hFull

/-- `bytesRegion` is PC-free — lets `runBlock`/`pcFree` discharge frame side-conditions. -/
instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/--
**`rlp_content_to_u64` — non-canonical failure path.**

A nonzero-length content with a leading zero byte (`0 < len ≤ 8 ∧ content[0] = 0`)
is a non-canonical scalar encoding; the routine returns value `a0 = 0` and status
`a1 = 3`. `content` is modeled as offset `srcOff` into the dword-aligned input
region `bytesRegion srcBase srcBytes` (`a0 = srcBase + srcOff`,
`content[0] = srcBytes[srcOff]`). Scratch `t0..t3` clobbered; `ra` and the input
region preserved.
-/
theorem rlp_content_to_u64_noncanonical_spec_within
    (base srcBase raVal t0Old t2Old t3Old : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen0 : 0 < len) (hlen8 : len ≤ 8)
    (hsalign : srcBase.toNat % 8 = 0) (hsoff : srcOff < srcBytes.length)
    (hsover : srcBase.toNat + srcOff < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hnoncanon : srcBytes[srcOff]'hsoff = 0) :
    cpsTripleWithin 10 base (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  have hnlt : ¬ (BitVec.ult (8 : Word) (BitVec.ofNat 64 len) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show BitVec.toNat (8 : Word) = 8 from by decide, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    omega
  have hlen_ne : (BitVec.ofNat 64 len : Word) ≠ 0 := by
    intro hc
    have h0 : (BitVec.ofNat 64 len : Word).toNat = 0 := by rw [hc]; rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)] at h0
    omega
  have hbyte0 : (srcBytes[srcOff]'hsoff).zeroExtend 64 = (0 : Word) := by rw [hnoncanon]; decide
  -- Phase A: LI x5 8 (idx 0).  base → base+4.
  have hLI := li_spec_gen_within .x5 t0Old (8 : Word) base (by decide)
  have hA : cpsTripleWithin 1 base (base + 4) (rlp_content_to_u64_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (8 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
    runBlock hLI
  -- Phase B: BLTU x5 x11 72 NOT taken (len ≤ 8), idx 1.  base+4 → base+8.
  have hbltu := bltu_spec_gen_within .x5 .x11 (72 : BitVec 13) (8 : Word) (BitVec.ofNat 64 len) (base + 4)
  rw [show (base + 4) + signExtend13 (72 : BitVec 13) = base + 76 from by
        rw [show signExtend13 (72 : BitVec 13) = (72 : Word) from by decide]; bv_omega,
      show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbltu
  have hmono1 : ∀ a i, CodeReq.singleton (base + 4) (.BLTU .x5 .x11 (72 : BitVec 13)) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 1 (base + 4)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hB := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono1 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hnlt ((sepConj_pure_right _).1 h_pure).2)
  -- Phase C: MV x6 x10 ; MV x7 x11 ; LI x10 0 (idx 2,3,4).  base+8 → base+20.
  have hmv6 := mv_spec_gen_within .x6 .x10 (srcBase + BitVec.ofNat 64 srcOff)
    (srcBase + BitVec.ofNat 64 srcOff) (base + 8) (by decide)
  have hmv7 := mv_spec_gen_within .x7 .x11 (BitVec.ofNat 64 len) t2Old (base + 12) (by decide)
  have hLI0 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (0 : Word) (base + 16) (by decide)
  have hC : cpsTripleWithin 3 (base + 8) (base + 20) (rlp_content_to_u64_code base)
      ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x7 ↦ᵣ t2Old) ** (.x11 ↦ᵣ BitVec.ofNat 64 len))
      ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 len) ** (.x11 ↦ᵣ BitVec.ofNat 64 len)) := by
    runBlock hmv6 hmv7 hLI0
  have hC' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (8 : Word)) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes)
    (by pcFree) hC
  -- Phase D: BEQ x7 x0 40 NOT taken (len > 0), idx 5.  base+20 → base+24.
  have hbe1 := beq_spec_gen_within .x7 .x0 (40 : BitVec 13) (BitVec.ofNat 64 len) (0 : Word) (base + 20)
  rw [show (base + 20) + signExtend13 (40 : BitVec 13) = base + 60 from by
        rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbe1
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.BEQ .x7 .x0 (40 : BitVec 13)) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 5 (base + 20)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hD := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono5 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      (by pcFree) hbe1))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hlen_ne ((sepConj_pure_right _).1 h_pure).2)
  -- Phase E: LBU x28 x6 0 (idx 6): x28 := content[0].  base+24 → base+28.
  have hlbu := bytesRegion_lbu_within .x28 .x6 srcBase t3Old (base + 24) srcBytes srcOff
    (by decide) hsalign hsoff hsover hsvalid
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega, hbyte0] at hlbu
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.LBU .x28 .x6 0) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 6 (base + 24)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hLBU := cpsTripleWithin_extend_code hmono6 (cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x7 ↦ᵣ BitVec.ofNat 64 len) **
      (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hlbu)
  -- Phase F: BEQ x28 x0 40 TAKEN (content[0] = 0), idx 7.  base+28 → base+68 (noncanon).
  have hbe2 := beq_spec_gen_within .x28 .x0 (40 : BitVec 13)
    ((srcBytes[srcOff]'hsoff).zeroExtend 64) (0 : Word) (base + 28)
  rw [hbyte0] at hbe2
  rw [show (base + 28) + signExtend13 (40 : BitVec 13) = base + 68 from by
        rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbe2
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.BEQ .x28 .x0 (40 : BitVec 13)) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 7 (base + 28)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hF := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono7 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 len) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbe2))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- Phase G: LI x11 3 ; ret (idx 17, 18).  base+68 → ra &&& ~~~1.
  have hLI3 := li_spec_gen_within .x11 (BitVec.ofNat 64 len) (3 : Word) (base + 68) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 72)
  simp only [signExtend12_0] at hRet
  have hG : cpsTripleWithin 2 (base + 68) (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (3 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI3 hRet
  have hG' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x7 ↦ᵣ BitVec.ofNat 64 len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes)
    (by pcFree) hG
  -- Compose A ⨾ B ⨾ C ⨾ D ⨾ E ⨾ F ⨾ G (dropping each true branch pure).
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s1 hC'
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s3 hLBU
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hF
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s5 hG'
  rw [show (1 + 1 + 3 + 1 + 1 + 1 + 2) = 10 from rfl] at s6
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s6
  have hp' := sepConj_mono_right (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x))))))) h hp
  xperm_hyp hp'

-- Sanity: program length + key instruction lookups.
example : rlp_content_to_u64_prog.length = 22 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u64_prog) 4 =
    some (.BLTU .x5 .x11 (72 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u64_prog) 76 =
    some (.LI .x10 (0 : Word)) := by decide

end EvmAsm.Rv64.RLP
