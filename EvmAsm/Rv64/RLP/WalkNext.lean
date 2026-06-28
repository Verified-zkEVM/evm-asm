/-
  EvmAsm.Rv64.RLP.WalkNext

  A verified RISC-V leaf subroutine: a CPS drop-in for the codegen guest function
  `rlp_walk_next` emitted by `EvmAsm/Codegen/Programs/RlpWalk.lean`
  (`rlpWalkNextFunction`, added in #9503's cursor-walk RLP decode work).

  `rlp_walk_next` decodes the single RLP item at the cursor, advances the cursor
  past it, and reports the item's content length. The content pointer is derived
  by the caller as `advanced_cursor - content_length`. It is a list/item-structure
  operation — it decodes no scalar value — so the scalar-canonicality rule
  (enforced in `ContentToU256Be`/`ContentToU64`) does not apply here; this is a
  *faithful* drop-in of the guest's per-form classification.

  ## Caller-facing contract (LP64)

  Frameless leaf: reached by `jal ra, rlp_walk_next`, returns via `ret`.

  ### Inputs
  * `a0` (`x10`) — cursor (current item, absolute pointer).
  * `a1` (`x11`) — end (exclusive, absolute pointer).

  ### Outputs
  * `a0` (`x10`) — advanced cursor (next item) — unchanged on end-of-list.
  * `a1` (`x11`) — **status**: `0` ok / `2` end-of-list.
  * `a2` (`x12`) — content length (byte-string items: prefix-stripped payload;
    sub-list items: full encoded span).

  Scratch `t0..t6` (`x5`,`x6`,`x7`,`x28`,`x29`,`x30`,`x31`) clobbered; `ra` preserved.

  ## Verification status

  Lays out the 64-instruction body `rlp_walk_next_prog`. **All six per-form cases**
  are proved as complete leaf-function Hoare triples (axiom-clean):
    * `…_end_spec_within` — `cursor ≥ end` → `a1 = 2`;
    * `…_single_spec_within` — `prefix < 0x80` → `a2 = 1`, cursor `+1`;
    * `…_short_string_spec_within` — `0x80 ≤ prefix < 0xb8` → `a2 = prefix-0x80`;
    * `…_long_string_spec_within` — `0xb8 ≤ prefix < 0xc0` → `a2 = decoded` (the
      big-endian length-field accumulation loop, `wn_ls_loop`);
    * `…_short_list_spec_within` — `0xc0 ≤ prefix < 0xf8` → `a2 = full span`;
    * `…_long_list_spec_within` — `prefix ≥ 0xf8` → `a2 = full span` (the
      length-field loop `wn_ll_loop`).

  A single unified disjunctive theorem is a follow-up: unlike the content/walk-init
  routines it is structurally awkward here, since the `end-of-list` branch
  (`cursor ≥ end`, no prefix read) has an *incompatible* precondition with the
  five prefix-reading branches, and the two long forms carry prefix-dependent
  length-field validity/step counts. The six per-form triples already fully
  specify the behavior.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP

/--
The verified drop-in body for the codegen guest `rlp_walk_next` (64 instructions).
Register map: `a0=x10`, `a1=x11`, `a2=x12`, `t0=x5`, `t1=x6`, `t2=x7`, `t3=x28`,
`t4=x29`, `t5=x30`, `t6=x31`, `ra=x1`.

Dispatches on the prefix byte: end-of-list / single (`<0x80`) / short string
(`0x80..0xb7`) / long string (`0xb8..0xbf`) / short list (`0xc0..0xf7`) / long
list (`0xf8..0xff`). The two long forms read the big-endian length field with a
`slli/lbu/or` loop. See the module doc for the per-form content/advance semantics.
-/
def rlp_walk_next_prog : List Instr :=
  [ .BGEU .x10 .x11 (244 : BitVec 13),  -- 0  cursor ≥ end → end
    .LBU .x5 .x10 0,                    -- 1  prefix
    .LI .x6 (0x80 : Word),              -- 2
    .BLTU .x5 .x6 (216 : BitVec 13),    -- 3  < 0x80 → single
    .LI .x6 (0xb8 : Word),              -- 4
    .BLTU .x5 .x6 (184 : BitVec 13),    -- 5  < 0xb8 → short string
    .LI .x6 (0xc0 : Word),              -- 6
    .BLTU .x5 .x6 (112 : BitVec 13),    -- 7  < 0xc0 → long string
    .LI .x6 (0xf8 : Word),              -- 8
    .BLTU .x5 .x6 (76 : BitVec 13),     -- 9  < 0xf8 → short list
    .LI .x6 (0xf7 : Word),              -- 10 long list
    .SUB .x7 .x5 .x6,                   -- 11 lol = prefix - 0xf7
    .LI .x28 (0 : Word),                -- 12 acc
    .MV .x29 .x7,                       -- 13 remaining
    .ADDI .x30 .x10 (1 : BitVec 12),    -- 14 first length byte ptr
    .BEQ .x29 .x0 (28 : BitVec 13),     -- 15 loop head: rem == 0 → ll_done
    .SLLI .x28 .x28 (8 : BitVec 6),     -- 16
    .LBU .x31 .x30 0,                   -- 17
    .OR .x28 .x28 .x31,                 -- 18
    .ADDI .x30 .x30 (1 : BitVec 12),    -- 19
    .ADDI .x29 .x29 (-1 : BitVec 12),   -- 20
    .JAL .x0 (-24 : BitVec 21),         -- 21 → idx 15
    .ADD .x31 .x7 .x28,                 -- 22 ll_done: lol + decoded
    .ADDI .x31 .x31 (1 : BitVec 12),    -- 23 span = 1 + lol + decoded
    .ADD .x10 .x10 .x31,                -- 24 advanced
    .MV .x12 .x31,                      -- 25 a2 = span
    .LI .x11 (0 : Word),                -- 26
    .JALR .x0 .x1 0,                    -- 27
    .LI .x6 (0xc0 : Word),              -- 28 short_list
    .SUB .x31 .x5 .x6,                  -- 29 prefix - 0xc0
    .ADDI .x31 .x31 (1 : BitVec 12),    -- 30 span
    .ADD .x10 .x10 .x31,                -- 31
    .MV .x12 .x31,                      -- 32
    .LI .x11 (0 : Word),                -- 33
    .JALR .x0 .x1 0,                    -- 34
    .LI .x6 (0xb7 : Word),              -- 35 long_string
    .SUB .x7 .x5 .x6,                   -- 36 lol = prefix - 0xb7
    .LI .x28 (0 : Word),                -- 37 acc
    .MV .x29 .x7,                       -- 38 remaining
    .ADDI .x30 .x10 (1 : BitVec 12),    -- 39 first length byte ptr
    .BEQ .x29 .x0 (28 : BitVec 13),     -- 40 loop head: rem == 0 → ls_done
    .SLLI .x28 .x28 (8 : BitVec 6),     -- 41
    .LBU .x31 .x30 0,                   -- 42
    .OR .x28 .x28 .x31,                 -- 43
    .ADDI .x30 .x30 (1 : BitVec 12),    -- 44
    .ADDI .x29 .x29 (-1 : BitVec 12),   -- 45
    .JAL .x0 (-24 : BitVec 21),         -- 46 → idx 40
    .ADD .x10 .x30 .x28,                -- 47 ls_done: advanced = content_start + decoded
    .MV .x12 .x28,                      -- 48 a2 = decoded
    .LI .x11 (0 : Word),                -- 49
    .JALR .x0 .x1 0,                    -- 50
    .LI .x6 (0x80 : Word),              -- 51 short_string
    .SUB .x12 .x5 .x6,                  -- 52 a2 = prefix - 0x80
    .ADDI .x10 .x10 (1 : BitVec 12),    -- 53
    .ADD .x10 .x10 .x12,                -- 54 advanced = cursor + 1 + len
    .LI .x11 (0 : Word),                -- 55
    .JALR .x0 .x1 0,                    -- 56
    .ADDI .x10 .x10 (1 : BitVec 12),    -- 57 single: advanced = cursor + 1
    .LI .x12 (1 : Word),                -- 58 a2 = 1
    .LI .x11 (0 : Word),                -- 59
    .JALR .x0 .x1 0,                    -- 60
    .LI .x11 (2 : Word),                -- 61 end: a1 = 2
    .LI .x12 (0 : Word),                -- 62 a2 = 0
    .JALR .x0 .x1 0 ]                   -- 63

theorem rlp_walk_next_prog_length : rlp_walk_next_prog.length = 64 := rfl

abbrev rlp_walk_next_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_walk_next_prog

instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/--
**`rlp_walk_next` — end-of-list path.**

When the cursor is at or past `end` (`cursor ≥ end`), there is no further item:
the routine returns status `a1 = 2`, content length `a2 = 0`, leaving the cursor
`a0` unchanged. No memory is touched; `ra` preserved.
-/
theorem rlp_walk_next_end_spec_within
    (base cursor endPtr raVal a2Old : Word)
    (h_end : ¬ BitVec.ult cursor endPtr) :
    cpsTripleWithin 4 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ cursor) ** (.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal)) := by
  -- Phase A: BGEU x10 x11 244 TAKEN (cursor ≥ end), idx 0.  base → base+244 (end).
  have hbgeu := bgeu_spec_gen_within .x10 .x11 (244 : BitVec 13) cursor endPtr base
  rw [show base + signExtend13 (244 : BitVec 13) = base + 244 from by
        rw [show signExtend13 (244 : BitVec 13) = (244 : Word) from by decide]] at hbgeu
  have hmono0 : ∀ a i, CodeReq.singleton base (.BGEU .x10 .x11 (244 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 0 base
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hB := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono0 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      (by pcFree) hbgeu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact h_end ((sepConj_pure_right _).1 h_pure).2)
  -- Phase C: LI x11 2 ; LI x12 0 ; ret (idx 61,62,63).  base+244 → ra &&& ~~~1.
  have hLI2 := li_spec_gen_within .x11 endPtr (2 : Word) (base + 244) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 248) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 252)
  simp only [signExtend12_0] at hRet
  have hC : cpsTripleWithin 3 (base + 244) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (2 : Word)) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI2 hLI0 hRet
  have hC' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ cursor) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) hC
  -- Compose A(taken) ⨾ C.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) hB hC'
  rw [show (1 + 3) = 4 from rfl] at s1
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s1

/-- Helper: `BGEU x10 x11` NOT taken (in-bounds), idx 0, `base → base+4`. -/
private theorem wn_bgeu_ntaken (base srcBase endPtr : Word)
    (srcOff : Nat) (R : Assertion) (hR : R.pcFree)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true) :
    cpsTripleWithin 1 base (base + 4) (rlp_walk_next_code base)
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr)) ** R)
      (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr)) ** R) := by
  have hbgeu := bgeu_spec_gen_within .x10 .x11 (244 : BitVec 13)
    (srcBase + BitVec.ofNat 64 srcOff) endPtr base
  have hmono0 : ∀ a i, CodeReq.singleton base (.BGEU .x10 .x11 (244 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 0 base
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have h := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono0 (cpsBranchWithin_frameR R hR hbgeu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 h_inb)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h' hp => sepConj_mono_left (sepConj_mono_right
      (fun h'' hp'' => ((sepConj_pure_right h'').1 hp'').1)) h' hp) h

/--
**`rlp_walk_next` — single-byte item path (`prefix < 0x80`).**

A single byte `< 0x80` is its own one-byte content: the cursor advances by one,
content length `a2 = 1`, status `a1 = 0`. Scratch `t0`/`t1` clobbered.
-/
theorem rlp_walk_next_single_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_single : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true) :
    cpsTripleWithin 8 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  -- Phase A: BGEU not taken (idx 0).  base → base+4.
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  -- Phase B: LBU x5 x10 0 ; LI x6 0x80 (idx 1,2).  base+4 → base+12.
  have hlbu := bytesRegion_lbu_within .x5 .x10 srcBase t0Old (base + 4) srcBytes srcOff
    (by decide) hsalign hoff hover hvalid
  have hLI := li_spec_gen_within .x6 t1Old (0x80 : Word) (base + 8) (by decide)
  have hB : cpsTripleWithin 2 (base + 4) (base + 12) (rlp_walk_next_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ (0x80 : Word)) **
        bytesRegion srcBase srcBytes) := by
    runBlock hlbu hLI
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  -- Phase C: BLTU x5 x6 216 TAKEN (prefix < 0x80), idx 3.  base+12 → base+228 (single).
  have hbltu := bltu_spec_gen_within .x5 .x6 (216 : BitVec 13)
    ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) (base + 12)
  rw [show (base + 12) + signExtend13 (216 : BitVec 13) = base + 228 from by
        rw [show signExtend13 (216 : BitVec 13) = (228 - 12 : Word) from by decide]; bv_omega,
      show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbltu
  have hmono3 : ∀ a i, CodeReq.singleton (base + 12) (.BLTU .x5 .x6 (216 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 3 (base + 12)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by rfl))
  have hC := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono3 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_single)
  -- Phase D: ADDI x10 x10 1 ; LI x12 1 ; LI x11 0 ; ret (idx 57..60).  base+228 → ra &&& ~~~1.
  have haddi := addi_spec_gen_same_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 228) (by decide)
  have hLI1 := li_spec_gen_within .x12 a2Old (1 : Word) (base + 232) (by decide)
  have hLI0 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 236) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 240)
  simp only [signExtend12_0] at hRet
  have hD : cpsTripleWithin 4 (base + 228) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x11 ↦ᵣ endPtr) **
        (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))) **
        (.x12 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock haddi hLI1 hLI0 hRet
  have hD' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0x80 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hD
  -- Compose A ⨾ B ⨾ C(taken) ⨾ D.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hD'
  rw [show (1 + 2 + 1 + 4) = 8 from rfl] at s3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s3
  have hp' := sepConj_mono_right (sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6) (fun _ x => x))) h hp
  xperm_hyp hp'

/--
**`rlp_walk_next` — short-string item path (`0x80 ≤ prefix < 0xb8`).**

A short RLP string has content length `a2 = prefix - 0x80`; the cursor advances
past the 1-byte prefix and the content (`a0 = cursor + 1 + a2`), status `a1 = 0`.
Scratch `t0`/`t1` clobbered.
-/
theorem rlp_walk_next_short_string_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true) :
    cpsTripleWithin 12 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ (((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) ** regOwn .x5 **
        regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  -- Phase A: BGEU not taken (idx 0).  base → base+4.
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  -- Phase B: LBU x5 x10 0 ; LI x6 0x80 (idx 1,2).  base+4 → base+12.
  have hlbu := bytesRegion_lbu_within .x5 .x10 srcBase t0Old (base + 4) srcBytes srcOff
    (by decide) hsalign hoff hover hvalid
  have hLIc := li_spec_gen_within .x6 t1Old (0x80 : Word) (base + 8) (by decide)
  have hB : cpsTripleWithin 2 (base + 4) (base + 12) (rlp_walk_next_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ (0x80 : Word)) **
        bytesRegion srcBase srcBytes) := by
    runBlock hlbu hLIc
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  -- Phase C: BLTU x5 x6 216 NOT taken (prefix ≥ 0x80), idx 3.  base+12 → base+16.
  have hbltu := bltu_spec_gen_within .x5 .x6 (216 : BitVec 13)
    ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) (base + 12)
  rw [show (base + 12) + signExtend13 (216 : BitVec 13) = base + 228 from by
        rw [show signExtend13 (216 : BitVec 13) = (228 - 12 : Word) from by decide]; bv_omega,
      show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbltu
  have hmono3 : ∀ a i, CodeReq.singleton (base + 12) (.BLTU .x5 .x6 (216 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 3 (base + 12)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by rfl))
  have hC := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono3 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_lo ((sepConj_pure_right _).1 h_pure).2)
  -- Phase D: LI x6 0xb8 (idx 4).  base+16 → base+20.
  have hLI8 := li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 16) (by decide)
  have hD : cpsTripleWithin 1 (base + 16) (base + 20) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0x80 : Word))) ((.x6 ↦ᵣ (0xb8 : Word))) := by
    runBlock hLI8
  have hD' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion srcBase srcBytes)
    (by pcFree) hD
  -- Phase E: BLTU x5 x6 184 TAKEN (prefix < 0xb8), idx 5.  base+20 → base+204 (short_string).
  have hbltu2 := bltu_spec_gen_within .x5 .x6 (184 : BitVec 13)
    ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) (base + 20)
  rw [show (base + 20) + signExtend13 (184 : BitVec 13) = base + 204 from by
        rw [show signExtend13 (184 : BitVec 13) = (204 - 20 : Word) from by decide]; bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbltu2
  have hmono5 : ∀ a i, CodeReq.singleton (base + 20) (.BLTU .x5 .x6 (184 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 5 (base + 20)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by rfl))
  have hE := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono5 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      (by pcFree) hbltu2))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hi)
  -- Phase F: LI x6 0x80 ; SUB x12 x5 x6 ; ADDI x10 x10 1 ; ADD x10 x10 x12 ; LI x11 0 ; ret
  -- (idx 51..56).  base+204 → ra &&& ~~~1.
  have hLI80 := li_spec_gen_within .x6 (0xb8 : Word) (0x80 : Word) (base + 204) (by decide)
  have hsub := sub_spec_gen_within .x12 .x5 .x6 ((srcBytes[srcOff]'hoff).zeroExtend 64)
    (0x80 : Word) a2Old (base + 208) (by decide)
  have haddi := addi_spec_gen_same_within .x10 (srcBase + BitVec.ofNat 64 srcOff) (1 : BitVec 12)
    (base + 212) (by decide)
  have hadd2 := add_spec_gen_rd_eq_rs1_within .x10 .x12
    ((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12))
    ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)) (base + 216) (by decide)
  have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 220) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 224)
  simp only [signExtend12_0] at hRet
  have hF : cpsTripleWithin 6 (base + 204) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xb8 : Word)) ** (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x1 ↦ᵣ raVal))
      ((.x6 ↦ᵣ (0x80 : Word)) **
        (.x12 ↦ᵣ ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word))) **
        (.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) **
        (.x10 ↦ᵣ (((srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)) +
          ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0x80 : Word)))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal)) := by
    runBlock hLI80 hsub haddi hadd2 hLI11 hRet
  have hF' := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) (by pcFree) hF
  -- Compose A ⨾ B ⨾ C ⨾ D ⨾ E(taken) ⨾ F.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s2 hD'
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hE
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s4 hF'
  rw [show (1 + 2 + 1 + 1 + 1 + 6) = 12 from rfl] at s5
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s5
  have hp' := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn .x5) (fun _ x => x)))) h hp
  xperm_hyp hp'

/-- `bytesRegion_lbu` packaged with the `LI x6 0x80` follow-on (idx 1,2). -/
private theorem wn_lbu_li80 (base srcBase : Word) (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (t0Old t1Old : Word) (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin 2 (base + 4) (base + 12) (rlp_walk_next_code base)
      ((.x5 ↦ᵣ t0Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion srcBase srcBytes)
      ((.x5 ↦ᵣ (srcBytes[srcOff]'hoff).zeroExtend 64) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x6 ↦ᵣ (0x80 : Word)) **
        bytesRegion srcBase srcBytes) := by
  have hlbu := bytesRegion_lbu_within .x5 .x10 srcBase t0Old (base + 4) srcBytes srcOff
    (by decide) hsalign hoff hover hvalid
  have hLIc := li_spec_gen_within .x6 t1Old (0x80 : Word) (base + 8) (by decide)
  runBlock hlbu hLIc

/-- One "BLTU x5 x6 off NOT taken (prefix ≥ thr)" cascade step over framed scratch
    `F`, leaving `x6` unchanged. -/
private theorem wn_cascade_step (base : Word) (off : BitVec 13) (idx : Nat) (a : Word)
    (pfx thr : Word) (F : Assertion) (hF : F.pcFree)
    (haddr : a = base + BitVec.ofNat 64 (4 * idx)) (hidx : idx < 64)
    (hinstr : rlp_walk_next_prog[idx]? = some (.BLTU .x5 .x6 off))
    (h_ge : ¬ BitVec.ult pfx thr = true) :
    cpsTripleWithin 1 a (a + 4) (rlp_walk_next_code base)
      (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ thr)) ** F)
      (((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ thr)) ** F) := by
  have hbltu := bltu_spec_gen_within .x5 .x6 off pfx thr a
  have hmono : ∀ x i, CodeReq.singleton a (.BLTU .x5 .x6 off) x = some i
      → rlp_walk_next_code base x = some i :=
    CodeReq.singleton_mono (by
      have hlk := CodeReq.ofProg_lookup_addr base rlp_walk_next_prog idx a hidx
        (by rw [rlp_walk_next_prog_length]; norm_num) haddr
      have hget : rlp_walk_next_prog.get ⟨idx, hidx⟩ = .BLTU .x5 .x6 off := by
        rw [List.get_eq_getElem]
        have he := List.getElem?_eq_getElem
          (show idx < rlp_walk_next_prog.length by rw [rlp_walk_next_prog_length]; exact hidx)
        rw [hinstr] at he
        exact (Option.some.inj he).symm
      rw [hget] at hlk; exact hlk)
  have hnt := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR F hF hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_ge ((sepConj_pure_right _).1 h_pure).2)
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h' hp => sepConj_mono_left (sepConj_mono_right
      (fun h'' hp'' => ((sepConj_pure_right h'').1 hp'').1)) h' hp) hnt

/--
**`rlp_walk_next` — short-list item path (`0xc0 ≤ prefix < 0xf8`).**

A short RLP sub-list is returned in full: content length `a2 = 1 + (prefix - 0xc0)`
(the full encoded span), cursor advances by the span, status `a1 = 0`. Scratch
`t0`/`t1`/`t6` clobbered.
-/
theorem rlp_walk_next_short_list_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t6Old : Word) (srcBytes : List (BitVec 8))
    (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true) :
    cpsTripleWithin 17 base (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) +
          (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) := by
  have h_lo80 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0x80 : Word).toNat = 128 from by decide,
      show (0xc0 : Word).toNat = 192 from by decide] at h_lo ⊢
    omega
  have h_lob8 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0xb8 : Word).toNat = 184 from by decide,
      show (0xc0 : Word).toNat = 192 from by decide] at h_lo ⊢
    omega
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  -- Common framed scratch for the cascade (everything except x5,x6).
  -- Phase A,B: BGEU nt ⨾ LBU x5 ; LI x6 0x80.  base → base+12.
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  have hB := wn_lbu_li80 base srcBase srcBytes srcOff t0Old t1Old hsalign hoff hover hvalid
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hB
  -- Cascade frame F (x10,x11,x12,x31,x0,x1,bytesRegion) wrapped to match wn_cascade_step.
  let F : Assertion := (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
    (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
    bytesRegion srcBase srcBytes
  -- Phase C: BLTU 216 nt (≥0x80), idx 3.  base+12 → base+16.
  have hC := wn_cascade_step base (216 : BitVec 13) 3 (base + 12) pfx (0x80 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo80)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hC
  -- Phase D: LI x6 0xb8 (idx 4).  base+16 → base+20.
  have hLI8 := li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 16) (by decide)
  have hmonoD : ∀ a i, CodeReq.singleton (base + 16) (.LI .x6 (0xb8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 4 (base + 16)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hD := cpsTripleWithin_extend_code hmonoD (cpsTripleWithin_frameR
    (((.x5 ↦ᵣ pfx)) ** F) (by pcFree) hLI8)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hD
  -- Phase E: BLTU 184 nt (≥0xb8), idx 5.  base+20 → base+24.
  have hE := wn_cascade_step base (184 : BitVec 13) 5 (base + 20) pfx (0xb8 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lob8)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hE
  -- Phase F: LI x6 0xc0 (idx 6).  base+24 → base+28.
  have hLIc := li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 24) (by decide)
  have hmonoF : ∀ a i, CodeReq.singleton (base + 24) (.LI .x6 (0xc0 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 6 (base + 24)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hF2 := cpsTripleWithin_extend_code hmonoF (cpsTripleWithin_frameR
    (((.x5 ↦ᵣ pfx)) ** F) (by pcFree) hLIc)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hF2
  -- Phase G: BLTU 112 nt (≥0xc0), idx 7.  base+28 → base+32.
  have hG := wn_cascade_step base (112 : BitVec 13) 7 (base + 28) pfx (0xc0 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hG
  -- Phase H: LI x6 0xf8 (idx 8).  base+32 → base+36.
  have hLIf := li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 32) (by decide)
  have hmonoH : ∀ a i, CodeReq.singleton (base + 32) (.LI .x6 (0xf8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 8 (base + 32)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hH := cpsTripleWithin_extend_code hmonoH (cpsTripleWithin_frameR
    (((.x5 ↦ᵣ pfx)) ** F) (by pcFree) hLIf)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hH
  -- Phase I: BLTU 76 TAKEN (prefix < 0xf8), idx 9.  base+36 → base+112 (short_list).
  have hbltu := bltu_spec_gen_within .x5 .x6 (76 : BitVec 13) pfx (0xf8 : Word) (base + 36)
  rw [show (base + 36) + signExtend13 (76 : BitVec 13) = base + 112 from by
        rw [show signExtend13 (76 : BitVec 13) = (76 : Word) from by decide]; bv_omega,
      show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hbltu
  have hmonoI : ∀ a i, CodeReq.singleton (base + 36) (.BLTU .x5 .x6 (76 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 9 (base + 36)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hI := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmonoI (cpsBranchWithin_frameR F (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hi)
  -- Phase J: short_list block (idx 28..34).  base+112 → ra &&& ~~~1.
  have hLIc0 := li_spec_gen_within .x6 (0xf8 : Word) (0xc0 : Word) (base + 112) (by decide)
  have hsub := sub_spec_gen_within .x31 .x5 .x6 pfx (0xc0 : Word) t6Old (base + 116) (by decide)
  have haddi := addi_spec_gen_same_within .x31 (pfx - (0xc0 : Word)) (1 : BitVec 12) (base + 120)
    (by decide)
  have hadd := add_spec_gen_rd_eq_rs1_within .x10 .x31 (srcBase + BitVec.ofNat 64 srcOff)
    ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) (base + 124) (by decide)
  have hmv := mv_spec_gen_within .x12 .x31
    ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) a2Old (base + 128) (by decide)
  have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 132) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 136)
  simp only [signExtend12_0] at hRet
  have hJ : cpsTripleWithin 7 (base + 112) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x31 ↦ᵣ t6Old) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x11 ↦ᵣ endPtr) **
        (.x1 ↦ᵣ raVal))
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) **
        (.x31 ↦ᵣ ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) +
          ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x12 ↦ᵣ ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x11 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal)) := by
    runBlock hLIc0 hsub haddi hadd hmv hLI11 hRet
  have hJ' := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hJ
  -- Compose A ⨾ B ⨾ C ⨾ D ⨾ E ⨾ F ⨾ G ⨾ H ⨾ I(taken) ⨾ J.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hE
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hF2
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hG
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hH
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hI
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s8 hJ'
  rw [show (1 + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 7) = 17 from rfl] at s9
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s9
  have hp' := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x)))) h hp
  rw [hpfx]
  xperm_hyp hp'

/-! ## Long-list length-field accumulation loop (idx 15..21) -/

/-- One iteration of the long-list length loop (idx 16..20), `base+64 → base+84`. -/
theorem wn_ll_body (base srcBase x28Old x31Old x29Val : Word) (srcBytes : List (BitVec 8)) (si : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hsi : si < srcBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true) :
    cpsTripleWithin 5 (base + 64) (base + 84) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ x28Old) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x31 ↦ᵣ x31Old) **
       (.x29 ↦ᵣ x29Val) ** bytesRegion srcBase srcBytes)
      ((.x28 ↦ᵣ ((x28Old <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi))) **
       (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi)) **
       (.x29 ↦ᵣ (x29Val + signExtend12 (-1 : BitVec 12))) ** bytesRegion srcBase srcBytes) := by
  have hslli := slli_spec_gen_same_within .x28 x28Old (8 : BitVec 6) (base + 64) (by nofun)
  rw [show (8 : BitVec 6).toNat = 8 from by decide] at hslli
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase x31Old (base + 68) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have hor := or_spec_gen_rd_eq_rs1_within .x28 .x31 (x28Old <<< (8 : Nat))
    (BitVec.setWidth 64 (srcBytes[si]'hsi)) (base + 72) (by nofun)
  have ha30 := addi_spec_gen_same_within .x30 (srcBase + BitVec.ofNat 64 si) 1 (base + 76) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have ha29 := addi_spec_gen_same_within .x29 x29Val (-1 : BitVec 12) (base + 80) (by nofun)
  runBlock hslli hlbu hor ha30 ha29

set_option maxRecDepth 8000 in
/-- The long-list length loop (idx 15..21), `base+60 → base+88`, by induction on the
    counter `x29`; accumulates `x28 = fromBytesBE` of the read length bytes. -/
theorem wn_ll_loop (base srcBase x31Old : Word) (srcBytes pre : List (BitVec 8)) (si n : Nat)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hbound : pre.length + n ≤ 8)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 60) (base + 88) (rlp_walk_next_code base)
      ((.x29 ↦ᵣ BitVec.ofNat 64 n) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      ((.x29 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))) **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 60) (.BEQ .x29 .x0 (28 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 15 (base + 60)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have ha_t : (base + 60) + signExtend13 (28 : BitVec 13) = base + 88 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 60 : Word) + 4 = base + 64 := by bv_omega
  induction n generalizing si pre x31Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 60)
    rw [ha_t, ha_f] at hbeq
    have htaken := cpsBranchWithin_takenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
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
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x31)))) h hq1
    xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 60)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
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
    have hx28tn : (BitVec.ofNat 64 (Nat.fromBytesBE pre)).toNat = Nat.fromBytesBE pre := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have body := wn_ll_body base srcBase (BitVec.ofNat 64 (Nat.fromBytesBE pre)) x31Old
      (BitVec.ofNat 64 (k + 1)) srcBytes si hsalign hsi0 (by omega) (hsvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have hbnd : Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 2 ^ 64 := by
      have h := Nat.fromBytesBE_lt (pre ++ [srcBytes[si]'hsi0])
      simp only [List.length_append, List.length_singleton] at h
      calc Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 256 ^ (pre.length + 1) := h
        _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 64 := by norm_num
    have hacc : ((BitVec.ofNat 64 (Nat.fromBytesBE pre) <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi0))
        = BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0])) := by
      apply BitVec.eq_of_toNat_eq
      rw [cu64_step _ _ (by rw [hx28tn]; exact hprelt), hx28tn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbnd, Nat.fromBytesBE_snoc]
    rw [hacc] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 84)
    have ha_back : (base + 84) + signExtend21 (-24 : BitVec 21) = base + 60 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 84) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_walk_next_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 21 (base + 84)
        (by rw [rlp_walk_next_prog_length]; norm_num)
        (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 84) (base + 60) (rlp_walk_next_code base)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
           (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
          (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k → isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have ihspec := ih (si := si + 1) (pre := pre ++ [srcBytes[si]'hsi0])
      (x31Old := BitVec.setWidth 64 (srcBytes[si]'hsi0)) (by omega) (by omega)
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
**`rlp_walk_next` — long-list item path (`prefix ≥ 0xf8`).**

A long RLP sub-list is returned in full. With `lol = prefix - 0xf7` length bytes
and `decoded = fromBytesBE` of those bytes, the content length (full span) is
`a2 = (lol + decoded) + 1`, and the cursor advances by it. Status `a1 = 0`.
Scratch `t0..t6` clobbered.
-/
theorem rlp_walk_next_long_list_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 22) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) +
          ((((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
              ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) + signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ ((((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
            BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
              ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) + signExtend12 (1 : BitVec 12))) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  have h_lo80 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0x80 : Word).toNat = 128 from by decide,
      show (0xf8 : Word).toNat = 248 from by decide] at h_lo ⊢
    omega
  have h_lob8 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0xb8 : Word).toNat = 184 from by decide,
      show (0xf8 : Word).toNat = 248 from by decide] at h_lo ⊢
    omega
  have h_loc0 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0xc0 : Word).toNat = 192 from by decide,
      show (0xf8 : Word).toNat = 248 from by decide] at h_lo ⊢
    omega
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xf7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  have hn8 : n ≤ 8 := by
    rw [hn]
    simp only [BitVec.ult, decide_eq_true_eq, show (0xf8 : Word).toNat = 248 from by decide] at h_lo
    have hpb : pfx.toNat < 256 := by
      rw [hpfx]; simp only [BitVec.toNat_setWidth]; have := (srcBytes[srcOff]'hoff).isLt; omega
    rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hxn : pfx - (0xf7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set spanw : Word := ((pfx - (0xf7 : Word)) + dec) + signExtend12 (1 : BitVec 12) with hspanw
  let F : Assertion := (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
    (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
    bytesRegion srcBase srcBytes
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  have hB := wn_lbu_li80 base srcBase srcBytes srcOff t0Old t1Old hsalign hoff hover hvalid
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  have hC := wn_cascade_step base (216 : BitVec 13) 3 (base + 12) pfx (0x80 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo80)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hC
  have hLI8 := li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 16) (by decide)
  have hmonoD : ∀ a i, CodeReq.singleton (base + 16) (.LI .x6 (0xb8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 4 (base + 16)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hD := cpsTripleWithin_extend_code hmonoD (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLI8)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hD
  have hE := wn_cascade_step base (184 : BitVec 13) 5 (base + 20) pfx (0xb8 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lob8)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hE
  have hLIc := li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 24) (by decide)
  have hmonoF : ∀ a i, CodeReq.singleton (base + 24) (.LI .x6 (0xc0 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 6 (base + 24)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hF2 := cpsTripleWithin_extend_code hmonoF (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLIc)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hF2
  have hG := wn_cascade_step base (112 : BitVec 13) 7 (base + 28) pfx (0xc0 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_loc0)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hG
  have hLIf := li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 32) (by decide)
  have hmonoH : ∀ a i, CodeReq.singleton (base + 32) (.LI .x6 (0xf8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 8 (base + 32)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hH := cpsTripleWithin_extend_code hmonoH (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLIf)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hH
  have hI := wn_cascade_step base (76 : BitVec 13) 9 (base + 36) pfx (0xf8 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo)
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hI
  have hLI7 := li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 40) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xf7 : Word) t2Old (base + 44) (by decide)
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 48) (by decide)
  have hmv29 := mv_spec_gen_within .x29 .x7 (pfx - (0xf7 : Word)) t4Old (base + 52) (by decide)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) 1 (base + 56)
    (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hSetup : cpsTripleWithin 5 (base + 40) (base + 60) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)))
      ((.x6 ↦ᵣ (0xf7 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff))) := by
    runBlock hLI7 hsub hLI28 hmv29 ha30
  have hSetup' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hSetup
  have hloop := wn_ll_loop base srcBase a2Old srcBytes [] (srcOff + 1) n hsalign
    (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover) (by simp; omega)
    (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0xf7 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  -- Post block (idx 22..27); consume the loop's `regOwn x31` via the forall-old lemma.
  have hPostV : ∀ x31Old, cpsTripleWithin 6 (base + 88) (raVal &&& ~~~1) (rlp_walk_next_code base)
      (((.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x11 ↦ᵣ endPtr) **
        (.x1 ↦ᵣ raVal)) ** (.x31 ↦ᵣ x31Old))
      ((.x31 ↦ᵣ spanw) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x28 ↦ᵣ dec) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 srcOff) + spanw)) ** (.x12 ↦ᵣ spanw) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    intro x31Old
    have hadd31 := add_spec_gen_within .x31 .x7 .x28 (pfx - (0xf7 : Word)) dec x31Old (base + 88)
      (by decide)
    have ha31 := addi_spec_gen_same_within .x31 ((pfx - (0xf7 : Word)) + dec) (1 : BitVec 12)
      (base + 92) (by decide)
    rw [← hspanw] at ha31
    have hadd10 := add_spec_gen_rd_eq_rs1_within .x10 .x31 (srcBase + BitVec.ofNat 64 srcOff)
      spanw (base + 96) (by decide)
    have hmv12 := mv_spec_gen_within .x12 .x31 spanw a2Old (base + 100) (by decide)
    have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 104) (by decide)
    have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 108)
    simp only [signExtend12_0] at hRet
    runBlock hadd31 ha31 hadd10 hmv12 hLI11 hRet
  have hPost := cpsTripleWithin_of_forall_regIs_to_regOwn hPostV
  have hPost' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0xf7 : Word)) ** (.x29 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion srcBase srcBytes) (by pcFree) hPost
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hE
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hF2
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hG
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 hH
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hI
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s8 hSetup'
  have s10 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s9 hloop'
  have s11 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s10 hPost'
  rw [show (1 + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 5 + (7 * n + 1) + 6) = 7 * n + 22 from by ring] at s11
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s11
  have hp' := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x31) (sepConj_mono (regIs_implies_regOwn .x7)
      (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)))) h hp
  have hp'' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x30)
        (fun _ x => x))))) h hp'
  xperm_hyp hp''

/-! ## Long-string length-field accumulation loop (idx 40..46) -/

/-- One iteration of the long-string length loop (idx 41..45), `base+164 → base+184`. -/
theorem wn_ls_body (base srcBase x28Old x31Old x29Val : Word) (srcBytes : List (BitVec 8)) (si : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hsi : si < srcBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true) :
    cpsTripleWithin 5 (base + 164) (base + 184) (rlp_walk_next_code base)
      ((.x28 ↦ᵣ x28Old) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x31 ↦ᵣ x31Old) **
       (.x29 ↦ᵣ x29Val) ** bytesRegion srcBase srcBytes)
      ((.x28 ↦ᵣ ((x28Old <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi))) **
       (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi)) **
       (.x29 ↦ᵣ (x29Val + signExtend12 (-1 : BitVec 12))) ** bytesRegion srcBase srcBytes) := by
  have hslli := slli_spec_gen_same_within .x28 x28Old (8 : BitVec 6) (base + 164) (by nofun)
  rw [show (8 : BitVec 6).toNat = 8 from by decide] at hslli
  have hlbu := bytesRegion_lbu_within .x31 .x30 srcBase x31Old (base + 168) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have hor := or_spec_gen_rd_eq_rs1_within .x28 .x31 (x28Old <<< (8 : Nat))
    (BitVec.setWidth 64 (srcBytes[si]'hsi)) (base + 172) (by nofun)
  have ha30 := addi_spec_gen_same_within .x30 (srcBase + BitVec.ofNat 64 si) 1 (base + 176) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have ha29 := addi_spec_gen_same_within .x29 x29Val (-1 : BitVec 12) (base + 180) (by nofun)
  runBlock hslli hlbu hor ha30 ha29

set_option maxRecDepth 8000 in
/-- The long-string length loop (idx 40..46), `base+160 → base+188`, by induction. -/
theorem wn_ls_loop (base srcBase x31Old : Word) (srcBytes pre : List (BitVec 8)) (si n : Nat)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hbound : pre.length + n ≤ 8)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 160) (base + 188) (rlp_walk_next_code base)
      ((.x29 ↦ᵣ BitVec.ofNat 64 n) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      ((.x29 ↦ᵣ (0 : Word)) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))) **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 160) (.BEQ .x29 .x0 (28 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 40 (base + 160)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have ha_t : (base + 160) + signExtend13 (28 : BitVec 13) = base + 188 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 160 : Word) + 4 = base + 164 := by bv_omega
  induction n generalizing si pre x31Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 160)
    rw [ha_t, ha_f] at hbeq
    have htaken := cpsBranchWithin_takenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
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
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x31)))) h hq1
    xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x29 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 160)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
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
    have hx28tn : (BitVec.ofNat 64 (Nat.fromBytesBE pre)).toNat = Nat.fromBytesBE pre := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have body := wn_ls_body base srcBase (BitVec.ofNat 64 (Nat.fromBytesBE pre)) x31Old
      (BitVec.ofNat 64 (k + 1)) srcBytes si hsalign hsi0 (by omega) (hsvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have hbnd : Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 2 ^ 64 := by
      have h := Nat.fromBytesBE_lt (pre ++ [srcBytes[si]'hsi0])
      simp only [List.length_append, List.length_singleton] at h
      calc Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 256 ^ (pre.length + 1) := h
        _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 64 := by norm_num
    have hacc : ((BitVec.ofNat 64 (Nat.fromBytesBE pre) <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi0))
        = BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0])) := by
      apply BitVec.eq_of_toNat_eq
      rw [cu64_step _ _ (by rw [hx28tn]; exact hprelt), hx28tn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbnd, Nat.fromBytesBE_snoc]
    rw [hacc] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 184)
    have ha_back : (base + 184) + signExtend21 (-24 : BitVec 21) = base + 160 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 184) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_walk_next_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 46 (base + 184)
        (by rw [rlp_walk_next_prog_length]; norm_num)
        (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 184) (base + 160) (rlp_walk_next_code base)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
           (.x29 ↦ᵣ BitVec.ofNat 64 k) ** (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
          (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k → isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have ihspec := ih (si := si + 1) (pre := pre ++ [srcBytes[si]'hsi0])
      (x31Old := BitVec.setWidth 64 (srcBytes[si]'hsi0)) (by omega) (by omega)
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
**`rlp_walk_next` — long-string item path (`0xb8 ≤ prefix < 0xc0`).**

A long RLP string is prefix-stripped: with `lol = prefix - 0xb7` length bytes and
`decoded = fromBytesBE` of them, the content length is `a2 = decoded` and the
cursor advances to `content_start + decoded`. Status `a1 = 0`. Scratch `t0..t6`
clobbered.
-/
theorem rlp_walk_next_long_string_spec_within
    (base srcBase endPtr raVal a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (h_inb : BitVec.ult (srcBase + BitVec.ofNat 64 srcOff) endPtr = true)
    (h_lo : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xb8 : Word) = true)
    (h_hi : BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (hllen : srcOff + 1 + ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat
      ≤ srcBytes.length)
    (hlover : srcBase.toNat + (srcOff + 1 +
      ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat →
      isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + 1 + k)) = true) :
    cpsTripleWithin (7 * ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat + 18) base
        (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 (srcOff + 1 +
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat)) +
          BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat)))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take
            ((srcBytes[srcOff]'hoff).zeroExtend 64 - (0xb7 : Word)).toNat))) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) := by
  have h_lo80 : ¬ BitVec.ult ((srcBytes[srcOff]'hoff).zeroExtend 64) (0x80 : Word) = true := by
    simp only [BitVec.ult, decide_eq_true_eq, show (0x80 : Word).toNat = 128 from by decide,
      show (0xb8 : Word).toNat = 184 from by decide] at h_lo ⊢
    omega
  set pfx := (srcBytes[srcOff]'hoff).zeroExtend 64 with hpfx
  set n : Nat := (pfx - (0xb7 : Word)).toNat with hn
  set dec : Word := BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop (srcOff + 1)).take n)) with hdec
  have hn8 : n ≤ 8 := by
    have hge : 184 ≤ pfx.toNat := by
      have h := h_lo
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt,
        show (0xb8 : Word).toNat = 184 from by decide] at h
      exact h
    have hlt : pfx.toNat < 192 := by
      have h := h_hi
      simpa only [BitVec.ult, decide_eq_true_eq, show (0xc0 : Word).toNat = 192 from by decide] using h
    rw [hn, BitVec.toNat_sub, show (0xb7 : Word).toNat = 183 from by decide]; omega
  have hxn : pfx - (0xb7 : Word) = BitVec.ofNat 64 n := by
    rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  let F : Assertion := (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
    (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
    (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
    bytesRegion srcBase srcBytes
  have hA := wn_bgeu_ntaken base srcBase endPtr srcOff
    ((.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) h_inb
  have hB := wn_lbu_li80 base srcBase srcBytes srcOff t0Old t1Old hsalign hoff hover hvalid
  have hB' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
      (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hB
  have hC := wn_cascade_step base (216 : BitVec 13) 3 (base + 12) pfx (0x80 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo80)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hC
  have hLI8 := li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 16) (by decide)
  have hmonoD : ∀ a i, CodeReq.singleton (base + 16) (.LI .x6 (0xb8 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 4 (base + 16)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hD := cpsTripleWithin_extend_code hmonoD (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLI8)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hD
  have hE := wn_cascade_step base (184 : BitVec 13) 5 (base + 20) pfx (0xb8 : Word) F (by pcFree)
    (by bv_omega) (by norm_num) (by rfl) (by rw [hpfx]; exact h_lo)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hE
  have hLIc := li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 24) (by decide)
  have hmonoF : ∀ a i, CodeReq.singleton (base + 24) (.LI .x6 (0xc0 : Word)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 6 (base + 24)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hF2 := cpsTripleWithin_extend_code hmonoF (cpsTripleWithin_frameR (((.x5 ↦ᵣ pfx)) ** F)
    (by pcFree) hLIc)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hF2
  -- Phase G: BLTU 112 TAKEN (prefix < 0xc0), idx 7.  base+28 → base+140 (long_string).
  have hbltu := bltu_spec_gen_within .x5 .x6 (112 : BitVec 13) pfx (0xc0 : Word) (base + 28)
  rw [show (base + 28) + signExtend13 (112 : BitVec 13) = base + 140 from by
        rw [show signExtend13 (112 : BitVec 13) = (112 : Word) from by decide]; bv_omega,
      show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbltu
  have hmonoG : ∀ a i, CodeReq.singleton (base + 28) (.BLTU .x5 .x6 (112 : BitVec 13)) a = some i
      → rlp_walk_next_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_next_prog 7 (base + 28)
      (by rw [rlp_walk_next_prog_length]; norm_num)
      (by rw [rlp_walk_next_prog_length]; norm_num) (by bv_omega))
  have hG := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmonoG (cpsBranchWithin_frameR F (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hi)
  -- Setup (idx 35..39): LI x6 0xb7 ; SUB x7 x5 x6 ; LI x28 0 ; MV x29 x7 ; ADDI x30 x10 1.
  -- base+140 → base+160.
  have hLI7 := li_spec_gen_within .x6 (0xc0 : Word) (0xb7 : Word) (base + 140) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xb7 : Word) t2Old (base + 144) (by decide)
  have hLI28 := li_spec_gen_within .x28 t3Old (0 : Word) (base + 148) (by decide)
  have hmv29 := mv_spec_gen_within .x29 .x7 (pfx - (0xb7 : Word)) t4Old (base + 152) (by decide)
  have ha30 := addi_spec_gen_within .x30 .x10 t5Old (srcBase + BitVec.ofNat 64 srcOff) 1 (base + 156)
    (by decide)
  rw [show (srcBase + BitVec.ofNat 64 srcOff) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (srcOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha30
  have hSetup : cpsTripleWithin 5 (base + 140) (base + 160) (rlp_walk_next_code base)
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)))
      ((.x6 ↦ᵣ (0xb7 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x28 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (pfx - (0xb7 : Word))) **
        (.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1))) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff))) := by
    runBlock hLI7 hsub hLI28 hmv29 ha30
  have hSetup' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) (by pcFree) hSetup
  have hloop := wn_ls_loop base srcBase t6Old srcBytes [] (srcOff + 1) n hsalign
    (by rw [hn] at hllen ⊢; exact hllen) (by rw [hn] at hlover ⊢; exact hlover) (by simp; omega)
    (by intro k hk; exact hlvalid k (by rw [hn] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hxn] at hloop
  have hloop' := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0xb7 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) ** (.x12 ↦ᵣ a2Old) **
      (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  -- Post (idx 47..50): ADD x10 x30 x28 ; MV x12 x28 ; LI x11 0 ; ret.  base+188 → ra &&& ~~~1.
  have hadd10 := add_spec_gen_within .x10 .x30 .x28
    (srcBase + BitVec.ofNat 64 (srcOff + 1 + n)) dec (srcBase + BitVec.ofNat 64 srcOff)
    (base + 188) (by decide)
  have hmv12 := mv_spec_gen_within .x12 .x28 dec a2Old (base + 192) (by decide)
  have hLI11 := li_spec_gen_within .x11 endPtr (0 : Word) (base + 196) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 200)
  simp only [signExtend12_0] at hRet
  have hPost : cpsTripleWithin 4 (base + 188) (raVal &&& ~~~1) (rlp_walk_next_code base)
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x28 ↦ᵣ dec) **
        (.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x12 ↦ᵣ a2Old) ** (.x11 ↦ᵣ endPtr) **
        (.x1 ↦ᵣ raVal))
      ((.x30 ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + 1 + n))) ** (.x28 ↦ᵣ dec) **
        (.x10 ↦ᵣ ((srcBase + BitVec.ofNat 64 (srcOff + 1 + n)) + dec)) ** (.x12 ↦ᵣ dec) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hadd10 hmv12 hLI11 hRet
  have hPost' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0xb7 : Word)) ** (.x7 ↦ᵣ (pfx - (0xb7 : Word))) **
      (.x29 ↦ᵣ (0 : Word)) ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
    (by pcFree) hPost
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA hB'
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hC
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hD
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hE
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hF2
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hG
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s6 hSetup'
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s7 hloop'
  have s9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s8 hPost'
  rw [show (1 + 2 + 1 + 1 + 1 + 1 + 1 + 5 + (7 * n + 1) + 4) = 7 * n + 18 from by ring] at s9
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s9
  have hp' := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x28)
      (fun _ x => x))) h hp
  have hp'' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x29)
        (fun _ x => x))))) h hp'
  xperm_hyp hp''

-- Sanity: program length + key instruction lookups.
example : rlp_walk_next_prog.length = 64 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_walk_next_prog) 0 =
    some (.BGEU .x10 .x11 (244 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_walk_next_prog) 244 =
    some (.LI .x11 (2 : Word)) := by decide

end EvmAsm.Rv64.RLP
