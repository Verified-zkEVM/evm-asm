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

  Lays out the 64-instruction body `rlp_walk_next_prog`. Proved: the
  **end-of-list** path (`cursor ≥ end`, status 2). Follow-ups (stacked-PR
  sequence): the single-byte / short-string / short-list paths (loop-free), the
  long-string / long-list paths (big-endian length-field accumulation loops), and
  the unified disjunctive theorem.
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
private theorem wn_bgeu_ntaken (base srcBase endPtr raVal a2Old t0Old t1Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat) (R : Assertion) (hR : R.pcFree)
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
  have hA := wn_bgeu_ntaken base srcBase endPtr raVal a2Old t0Old t1Old srcBytes srcOff
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

-- Sanity: program length + key instruction lookups.
example : rlp_walk_next_prog.length = 64 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_walk_next_prog) 0 =
    some (.BGEU .x10 .x11 (244 : BitVec 13)) := by decide
example : (CodeReq.ofProg (0 : Word) rlp_walk_next_prog) 244 =
    some (.LI .x11 (2 : Word)) := by decide

end EvmAsm.Rv64.RLP
