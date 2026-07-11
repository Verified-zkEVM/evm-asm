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
  **All four behavioral cases** are proved (axiom-clean):
    * `…_too_long_spec_within` — `len > 8`, status 2;
    * `…_noncanonical_spec_within` — `0 < len ≤ 8 ∧ content[0] = 0`, status 3;
    * `…_empty_spec_within` — `len = 0` (canonical zero), status 0, value `0`;
    * `…_success_spec_within` — `0 < len ≤ 8 ∧ content[0] ≠ 0`, status 0, value
      `a0 = fromBytesBE content` (the big-endian accumulation loop).
  The unified dispatch theorem `…_spec_within` combines all four with static
  preconditions and a four-way postcondition disjunction (per `AGENTS.md`).

  The scratch register `t1`/`x6` takes an **arbitrary** incoming value `x6Old`
  in every precondition (the routine's own `MV x6 x10` at index 2 overwrites it
  before first use), so callers need not pin it — this generalizes the original
  sound-but-slightly-strong `x6 = contentPtr` scratch assumption.
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
open EvmAsm.EL.RLP

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
`content[0] = srcBytes[srcOff]`). Scratch `t0..t3` (with arbitrary incoming
values) clobbered; `ra` and the input region preserved.
-/
theorem rlp_content_to_u64_noncanonical_spec_within
    (base srcBase raVal t0Old x6Old t2Old t3Old : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen0 : 0 < len) (hlen8 : len ≤ 8)
    (hsalign : srcBase.toNat % 8 = 0) (hsoff : srcOff < srcBytes.length)
    (hsover : srcBase.toNat + srcOff < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (hnoncanon : srcBytes[srcOff]'hsoff = 0) :
    cpsTripleWithin 10 base (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
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
        (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (8 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
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
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ x6Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hnlt ((sepConj_pure_right _).1 h_pure).2)
  -- Phase C: MV x6 x10 ; MV x7 x11 ; LI x10 0 (idx 2,3,4).  base+8 → base+20.
  have hmv6 := mv_spec_gen_within .x6 .x10 (srcBase + BitVec.ofNat 64 srcOff)
    x6Old (base + 8) (by decide)
  have hmv7 := mv_spec_gen_within .x7 .x11 (BitVec.ofNat 64 len) t2Old (base + 12) (by decide)
  have hLI0 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (0 : Word) (base + 16) (by decide)
  have hC : cpsTripleWithin 3 (base + 8) (base + 20) (rlp_content_to_u64_code base)
      ((.x6 ↦ᵣ x6Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
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

/-! ## Success path (`0 < len ≤ 8`): the big-endian accumulation loop -/

/-- Disjoint `or = add` for a left-shifted-by-8 value and a low byte. -/
theorem nat_lor_mul256 (x y : Nat) (hy : y < 256) : (x * 256) ||| y = x * 256 + y := by
  have h256 : (256 : Nat) = 2 ^ 8 := by norm_num
  rw [h256] at hy ⊢
  have hd : (x * 2 ^ 8 ||| y) / 2 ^ 8 = x := by
    rw [Nat.or_div_two_pow, Nat.mul_div_cancel _ (by positivity), Nat.div_eq_of_lt hy, Nat.or_zero]
  have hm : (x * 2 ^ 8 ||| y) % 2 ^ 8 = y := by
    rw [Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.mod_eq_of_lt hy, Nat.zero_or]
  calc x * 2 ^ 8 ||| y
      = ((x * 2 ^ 8 ||| y) / 2 ^ 8) * 2 ^ 8 + (x * 2 ^ 8 ||| y) % 2 ^ 8 := (Nat.div_add_mod' _ _).symm
    _ = x * 2 ^ 8 + y := by rw [hd, hm]

/-- One big-endian accumulation step: `(a <<< 8) ||| b = a*256 + b` (as `toNat`). -/
theorem cu64_step (a : BitVec 64) (b : BitVec 8) (ha : a.toNat < 2 ^ 56) :
    ((a <<< (8 : Nat)) ||| BitVec.setWidth 64 b).toNat = a.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  have hsh : (a.toNat <<< 8) % 2 ^ 64 = a.toNat * 256 := by
    rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from by norm_num]
    exact Nat.mod_eq_of_lt (by omega)
  have hb : b.toNat % 2 ^ 64 = b.toNat := Nat.mod_eq_of_lt (by have := b.isLt; omega)
  rw [hsh, hb]
  exact nat_lor_mul256 a.toNat b.toNat b.isLt

set_option maxRecDepth 8000 in
/-- One copy/accumulate iteration (idx 9..13, `base+36 → base+56`): `a0 <<= 8`,
    load `src[si]`, `a0 |= byte`, advance the src pointer, decrement the counter. -/
theorem cu64_body_spec_within
    (base srcBase x10Old x28Old x7Val : Word) (srcBytes : List (BitVec 8)) (si : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hsi : si < srcBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true) :
    cpsTripleWithin 5 (base + 36) (base + 56) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ x10Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x28 ↦ᵣ x28Old) **
       (.x7 ↦ᵣ x7Val) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((x10Old <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi))) **
       (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi)) **
       (.x7 ↦ᵣ (x7Val + signExtend12 (-1 : BitVec 12))) ** bytesRegion srcBase srcBytes) := by
  have hslli := slli_spec_gen_same_within .x10 x10Old (8 : BitVec 6) (base + 36) (by nofun)
  rw [show (8 : BitVec 6).toNat = 8 from by decide] at hslli
  have hlbu := bytesRegion_lbu_within .x28 .x6 srcBase x28Old (base + 40) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have hor := or_spec_gen_rd_eq_rs1_within .x10 .x28 (x10Old <<< (8 : Nat))
    (BitVec.setWidth 64 (srcBytes[si]'hsi)) (base + 44) (by nofun)
  have ha6 := addi_spec_gen_same_within .x6 (srcBase + BitVec.ofNat 64 si) 1 (base + 48) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha6
  have ha7 := addi_spec_gen_same_within .x7 x7Val (-1 : BitVec 12) (base + 52) (by nofun)
  runBlock hslli hlbu hor ha6 ha7

set_option maxRecDepth 8000 in
/-- **The accumulation loop (idx 8..14), `base+32 → base+60`, by induction on the
    counter.** Carries the already-processed prefix `pre` in `x10 = fromBytesBE pre`;
    after `n` more bytes (`(srcBytes.drop si).take n`), `x10 = fromBytesBE (pre ++ …)`.
    The total decoded width is bounded by 8 bytes (`pre.length + n ≤ 8`), so the
    `u64` never overflows. -/
theorem cu64_loop_spec_within
    (base srcBase x28Old : Word) (srcBytes pre : List (BitVec 8)) (si n : Nat)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hbound : pre.length + n ≤ 8)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 32) (base + 60) (rlp_content_to_u64_code base)
      ((.x7 ↦ᵣ BitVec.ofNat 64 n) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x28 ↦ᵣ x28Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      ((.x7 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))) **
       regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 32) (.BEQ .x7 .x0 (28 : BitVec 13)) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 8 (base + 32)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have ha_t : (base + 32) + signExtend13 (28 : BitVec 13) = base + 60 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 32 : Word) + 4 = base + 36 := by bv_omega
  induction n generalizing si pre x28Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x7 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 32)
    rw [ha_t, ha_f] at hbeq
    have htaken := cpsBranchWithin_takenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x28 ↦ᵣ x28Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htaken
    rw [show (0#64 : Word) = 0 from by decide] at hq
    simp only [Nat.add_zero, List.take_zero, List.append_nil]
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    have hq2 := sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x28)))) h hq1
    xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x7 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 32)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x28 ↦ᵣ x28Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hsi0 : si < srcBytes.length := by omega
    have hprelt : Nat.fromBytesBE pre < 2 ^ 56 := by
      have := Nat.fromBytesBE_lt pre
      have hpl : pre.length ≤ 7 := by omega
      calc Nat.fromBytesBE pre < 256 ^ pre.length := this
        _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hpl
        _ = 2 ^ 56 := by norm_num
    have hx10tn : (BitVec.ofNat 64 (Nat.fromBytesBE pre)).toNat = Nat.fromBytesBE pre := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    -- body (idx 9..13): a0 <<= 8, load byte, a0 |= byte, advance ptr, decrement counter.
    have body := cu64_body_spec_within base srcBase (BitVec.ofNat 64 (Nat.fromBytesBE pre)) x28Old
      (BitVec.ofNat 64 (k + 1)) srcBytes si hsalign hsi0 (by omega) (hsvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    -- the new accumulator value: fromBytesBE (pre ++ [srcBytes[si]]).
    have hbnd : Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 2 ^ 64 := by
      have h := Nat.fromBytesBE_lt (pre ++ [srcBytes[si]'hsi0])
      simp only [List.length_append, List.length_singleton] at h
      calc Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 256 ^ (pre.length + 1) := h
        _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 64 := by norm_num
    have hacc : ((BitVec.ofNat 64 (Nat.fromBytesBE pre) <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi0))
        = BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0])) := by
      apply BitVec.eq_of_toNat_eq
      rw [cu64_step _ _ (by rw [hx10tn]; exact hprelt), hx10tn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbnd, Nat.fromBytesBE_snoc]
    rw [hacc] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    -- jal back-edge (idx 14): base+56 → base+32.
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 56)
    have ha_back : (base + 56) + signExtend21 (-24 : BitVec 21) = base + 32 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 56) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_content_to_u64_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 14 (base + 56)
        (by rw [rlp_content_to_u64_prog_length]; norm_num)
        (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 56) (base + 32) (rlp_content_to_u64_code base)
        ((.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x7 ↦ᵣ BitVec.ofNat 64 k) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
        ((.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x7 ↦ᵣ BitVec.ofNat 64 k) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
           (.x7 ↦ᵣ BitVec.ofNat 64 k) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
          (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k → isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have ihspec := ih (si := si + 1) (pre := pre ++ [srcBytes[si]'hsi0])
      (x28Old := BitVec.setWidth 64 (srcBytes[si]'hsi0)) (by omega) (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega) hsvalid'
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hA1 body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hslice : pre ++ (srcBytes.drop si).take (k + 1)
        = (pre ++ [srcBytes[si]'hsi0]) ++ (srcBytes.drop (si + 1)).take k := by
      rw [List.drop_eq_getElem_cons hsi0, List.take_succ_cons, List.append_assoc,
        List.singleton_append]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega, hslice]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s1234

/--
**`rlp_content_to_u64` — success path (`0 < len ≤ 8`, canonical).**

For a canonical nonzero scalar (`0 < len ≤ 8` and high byte `content[0] ≠ 0`),
the `len` content bytes at `a0 = srcBase + srcOff` are decoded big-endian into
`a0 = fromBytesBE content`, status `a1 = 0`. Scratch `t0..t3` (with arbitrary
incoming values — in particular `t1`/`x6` is NOT pinned; the routine's own
`MV x6 x10` overwrites it) clobbered; `ra` and the input region preserved.
-/
theorem rlp_content_to_u64_success_spec_within
    (base srcBase raVal t0Old x6Old t2Old t3Old : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen0 : 0 < len) (hlen8 : len ≤ 8)
    (hsalign : srcBase.toNat % 8 = 0) (hsoff : srcOff < srcBytes.length)
    (hcanon : srcBytes[srcOff]'hsoff ≠ 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (7 * len + 11) base (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
        (.x11 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  have hnlt : ¬ (BitVec.ult (8 : Word) (BitVec.ofNat 64 len) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
      show BitVec.toNat (8 : Word) = 8 from by decide, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
    omega
  have hlen_ne : (BitVec.ofNat 64 len : Word) ≠ 0 := by
    intro hc
    have h0 : (BitVec.ofNat 64 len : Word).toNat = 0 := by rw [hc]; rfl
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)] at h0
    omega
  have hx28ne : (srcBytes[srcOff]'hsoff).zeroExtend 64 ≠ (0 : Word) := by
    intro hc
    apply hcanon
    apply BitVec.eq_of_toNat_eq
    have h := congrArg BitVec.toNat hc
    have hb : (srcBytes[srcOff]'hsoff).toNat < 256 := (srcBytes[srcOff]'hsoff).isLt
    simp only [BitVec.toNat_setWidth, show (0 : Word).toNat = 0 from by decide,
      show (0 : BitVec 8).toNat = 0 from by decide] at h ⊢
    omega
  -- Phase A: LI x5 8 (idx 0).  base → base+4.
  have hLI := li_spec_gen_within .x5 t0Old (8 : Word) base (by decide)
  have hA : cpsTripleWithin 1 base (base + 4) (rlp_content_to_u64_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (8 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
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
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ x6Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hnlt ((sepConj_pure_right _).1 h_pure).2)
  -- Phase C: MV x6 x10 ; MV x7 x11 ; LI x10 0 (idx 2,3,4).  base+8 → base+20.
  have hmv6 := mv_spec_gen_within .x6 .x10 (srcBase + BitVec.ofNat 64 srcOff)
    x6Old (base + 8) (by decide)
  have hmv7 := mv_spec_gen_within .x7 .x11 (BitVec.ofNat 64 len) t2Old (base + 12) (by decide)
  have hLI0 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (0 : Word) (base + 16) (by decide)
  have hC : cpsTripleWithin 3 (base + 8) (base + 20) (rlp_content_to_u64_code base)
      ((.x6 ↦ᵣ x6Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
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
    (by decide) hsalign hsoff (by omega) (hsvalid 0 hlen0)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hlbu
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.LBU .x28 .x6 0) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 6 (base + 24)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hLBU := cpsTripleWithin_extend_code hmono6 (cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x7 ↦ᵣ BitVec.ofNat 64 len) **
      (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hlbu)
  -- Phase F: BEQ x28 x0 40 NOT taken (content[0] ≠ 0), idx 7.  base+28 → base+32.
  have hbe2 := beq_spec_gen_within .x28 .x0 (40 : BitVec 13)
    ((srcBytes[srcOff]'hsoff).zeroExtend 64) (0 : Word) (base + 28)
  rw [show (base + 28) + signExtend13 (40 : BitVec 13) = base + 68 from by
        rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbe2
  have hmono7 : ∀ a i, CodeReq.singleton (base + 28) (.BEQ .x28 .x0 (40 : BitVec 13)) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 7 (base + 28)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hF := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono7 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x7 ↦ᵣ BitVec.ofNat 64 len) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      (by pcFree) hbe2))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hx28ne ((sepConj_pure_right _).1 h_pure).2)
  -- Loop (idx 8..14): accumulate len bytes big-endian.  base+32 → base+60.
  have hloop := cu64_loop_spec_within base srcBase ((srcBytes[srcOff]'hsoff).zeroExtend 64) srcBytes []
    srcOff len hsalign hslen hsover (by simp; omega) hsvalid
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (8 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hloop
  -- Phase G: LI x11 0 ; ret (idx 15, 16).  base+60 → ra &&& ~~~1.
  have hLI0' := li_spec_gen_within .x11 (BitVec.ofNat 64 len) (0 : Word) (base + 60) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 64)
  simp only [signExtend12_0] at hRet
  have hG : cpsTripleWithin 2 (base + 60) (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI0' hRet
  have hG' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
      (.x5 ↦ᵣ (8 : Word)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + len))) **
      (.x7 ↦ᵣ (0 : Word)) ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hG
  -- Compose A ⨾ B ⨾ C ⨾ D ⨾ E ⨾ F ⨾ loop ⨾ G (dropping each true branch pure).
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
    xperm_hyp hp2) s5 hloop'
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hG'
  rw [show (1 + 1 + 3 + 1 + 1 + 1 + (7 * len + 1) + 2) = 7 * len + 11 from by ring] at s7
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s7
  have hp' := sepConj_mono_right (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (fun _ x => x))))) h hp
  xperm_hyp hp'

/--
**`rlp_content_to_u64` — empty / canonical-zero path (`len = 0`).**

The empty byte string is the canonical encoding of `0`: the routine returns
value `a0 = 0`, status `a1 = 0`, reading no content (the `len == 0` short-circuit
fires before the high-byte check). Scratch `t0..t2` clobbered; `t3`, `ra`
preserved.
-/
theorem rlp_content_to_u64_empty_spec_within
    (base srcBase raVal t0Old x6Old t2Old t3Old : Word) (srcOff : Nat) :
    cpsTripleWithin 8 base (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hnlt : ¬ (BitVec.ult (8 : Word) (0 : Word) = true) := by decide
  -- Phase A: LI x5 8 (idx 0).  base → base+4.
  have hLI := li_spec_gen_within .x5 t0Old (8 : Word) base (by decide)
  have hA : cpsTripleWithin 1 base (base + 4) (rlp_content_to_u64_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      ((.x5 ↦ᵣ (8 : Word)) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI
  -- Phase B: BLTU x5 x11 72 NOT taken (0 ≤ 8), idx 1.  base+4 → base+8.
  have hbltu := bltu_spec_gen_within .x5 .x11 (72 : BitVec 13) (8 : Word) (0 : Word) (base + 4)
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
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ x6Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hnlt ((sepConj_pure_right _).1 h_pure).2)
  -- Phase C: MV x6 x10 ; MV x7 x11 ; LI x10 0 (idx 2,3,4).  base+8 → base+20.
  have hmv6 := mv_spec_gen_within .x6 .x10 (srcBase + BitVec.ofNat 64 srcOff)
    x6Old (base + 8) (by decide)
  have hmv7 := mv_spec_gen_within .x7 .x11 (0 : Word) t2Old (base + 12) (by decide)
  have hLI0 := li_spec_gen_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (0 : Word) (base + 16) (by decide)
  have hC : cpsTripleWithin 3 (base + 8) (base + 20) (rlp_content_to_u64_code base)
      ((.x6 ↦ᵣ x6Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
        (.x7 ↦ᵣ t2Old) ** (.x11 ↦ᵣ (0 : Word)))
      ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x10 ↦ᵣ (0 : Word)) **
        (.x7 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word))) := by
    runBlock hmv6 hmv7 hLI0
  have hC' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (8 : Word)) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hC
  -- Phase D: BEQ x7 x0 40 TAKEN (x7 = 0), idx 5.  base+20 → base+60 (done).
  have hbe1 := beq_spec_gen_within .x7 .x0 (40 : BitVec 13) (0 : Word) (0 : Word) (base + 20)
  rw [show (base + 20) + signExtend13 (40 : BitVec 13) = base + 60 from by
        rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]; bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbe1
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.BEQ .x7 .x0 (40 : BitVec 13)) a = some i
      → rlp_content_to_u64_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_content_to_u64_prog 5 (base + 20)
      (by rw [rlp_content_to_u64_prog_length]; norm_num)
      (by rw [rlp_content_to_u64_prog_length]; norm_num) (by rfl))
  have hD := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono5 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ t3Old) ** (.x1 ↦ᵣ raVal))
      (by pcFree) hbe1))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- Phase G: LI x11 0 ; ret (idx 15, 16).  base+60 → ra &&& ~~~1.
  have hLI0' := li_spec_gen_within .x11 (0 : Word) (0 : Word) (base + 60) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 64)
  simp only [signExtend12_0] at hRet
  have hG : cpsTripleWithin 2 (base + 60) (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI0' hRet
  have hG' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (8 : Word)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) **
      (.x7 ↦ᵣ (0 : Word)) ** (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcFree) hG
  -- Compose A ⨾ B ⨾ C ⨾ D(taken) ⨾ G.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s1 hC'
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s3 hG'
  rw [show (1 + 1 + 3 + 1 + 2) = 8 from rfl] at s4
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s4
  have hp' := sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
        (fun _ x => x)))))) h hp
  xperm_hyp hp'

/--
**Unified spec for `rlp_content_to_u64`.**

Per the `AGENTS.md` spec-design convention: every precondition is statically
known before the run (alignment, the buffer holds the `len`-byte content, size
bounds, byte-validity), and the outcome (value `a0` + status `a1`) is a four-way
postcondition disjunction. Single static step bound `7 * len + 11`, covering all
paths via `cpsTripleWithin_mono_nSteps`:

* `8 < len`  → `a1 = 2`, `a0 = 0` (too long);
* `len = 0`  → `a1 = 0`, `a0 = 0` (canonical zero);
* `0 < len ≤ 8 ∧ content[0] = 0` → `a1 = 3`, `a0 = 0` (non-canonical);
* `0 < len ≤ 8 ∧ content[0] ≠ 0` → `a1 = 0`, `a0 = fromBytesBE content`.

(`t1`/`x6` takes an arbitrary incoming value `x6Old` — the routine's own
`MV x6 x10` at index 2 overwrites it before first use.)
-/
theorem rlp_content_to_u64_spec_within
    (base srcBase raVal t0Old x6Old t2Old t3Old : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (7 * len + 11) base (raVal &&& ~~~1) (rlp_content_to_u64_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
       (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
            (.x11 ↦ᵣ (0 : Word)) ** ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) := by
  by_cases htl : 8 < len
  · -- too-long (status 2)
    have htl' : BitVec.ult (8 : Word) (BitVec.ofNat 64 len) = true := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
        show BitVec.toNat (8 : Word) = 8 from by decide, Nat.mod_eq_of_lt hlen64]
      omega
    have ht := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
       bytesRegion srcBase srcBytes)
      (by pcFree)
      (rlp_content_to_u64_too_long_spec_within base (srcBase + BitVec.ofNat 64 srcOff)
        (BitVec.ofNat 64 len) t0Old raVal htl')
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
    have hp1 := sepConj_mono
      (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x5) (fun _ x => x))))
      (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x))))
      h hp
    refine sepConj_mono_right (fun h' hbody => Or.inl
      (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, htl⟩) h' hbody)) h ?_
    xperm_hyp hp1
  · by_cases h0 : len = 0
    · -- empty (status 0)
      subst h0
      have he := cpsTripleWithin_frameR (bytesRegion srcBase srcBytes) (by pcFree)
        (rlp_content_to_u64_empty_spec_within base srcBase raVal t0Old x6Old t2Old t3Old srcOff)
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by
          simp only [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hp ⊢; xperm_hyp hp)
          (fun h hp => ?_) he)
      refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inl
        (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, rfl⟩) h' hbody))) h ?_
      xperm_hyp hp
    · by_cases hc : getByteAt srcBytes srcOff = 0
      · -- non-canonical (status 3)
        have hlen0 : 0 < len := Nat.pos_of_ne_zero h0
        have hsoff : srcOff < srcBytes.length := by omega
        have hgb : srcBytes[srcOff]'hsoff = getByteAt srcBytes srcOff := by simp [getByteAt, hsoff]
        have hnoncanon : srcBytes[srcOff]'hsoff = 0 := by rw [hgb]; exact hc
        have hnc := rlp_content_to_u64_noncanonical_spec_within base srcBase raVal t0Old x6Old t2Old t3Old
          srcBytes srcOff len hlen0 (by omega) hsalign hsoff (by omega) (by
            have := hsvalid 0 hlen0; rwa [Nat.add_zero] at this) hnoncanon
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hnc)
        refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inl
          (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hlen0, hc⟩) h' hbody)))) h ?_
        xperm_hyp hp
      · -- success (status 0)
        have hlen0 : 0 < len := Nat.pos_of_ne_zero h0
        have hsoff : srcOff < srcBytes.length := by omega
        have hgb : srcBytes[srcOff]'hsoff = getByteAt srcBytes srcOff := by simp [getByteAt, hsoff]
        have hcanon : srcBytes[srcOff]'hsoff ≠ 0 := by rw [hgb]; exact hc
        have hs := rlp_content_to_u64_success_spec_within base srcBase raVal t0Old x6Old t2Old t3Old
          srcBytes srcOff len hlen0 (by omega) hsalign hsoff hcanon hslen hsover hsvalid
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hs)
        refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inr
          (sepConj_mono_right (fun h'' hb => (sepConj_pure_right h'').2 ⟨hb, hlen0, hc⟩) h' hbody)))) h ?_
        xperm_hyp hp

-- Sanity: program length + key instruction lookups.
example : rlp_content_to_u64_prog.length = 22 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u64_prog) 4 =
    some (.BLTU .x5 .x11 (72 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_content_to_u64_prog) 76 =
    some (.LI .x10 (0 : Word)) := by decide

end EvmAsm.Rv64.RLP
