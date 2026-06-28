/-
  EvmAsm.Rv64.RLP.WalkInit

  A verified RISC-V leaf subroutine: a CPS drop-in for the codegen guest function
  `rlp_walk_init` emitted by `EvmAsm/Codegen/Programs/RlpWalk.lean`
  (`rlpWalkInitFunction`, added in #9503's cursor-walk RLP decode work).

  `rlp_walk_init` skips the outer RLP **list** prefix (`0xc0..0xff`) so the cursor
  points at the first encoded child item. It is a list-structure operation — it
  decodes no scalar — so the scalar-canonicality rule (enforced in
  `ContentToU256Be`/`ContentToU64`) does not apply here; this is a *faithful*
  drop-in of the guest's prefix classification.

  ## Caller-facing contract (LP64)

  Frameless leaf: reached by `jal ra, rlp_walk_init`, returns via `ret`.

  ### Inputs
  * `a0` (`x10`) — list bytes pointer (start of the outer list prefix).
  * `a1` (`x11`) — total list byte length (full encoded item).

  ### Outputs
  * `a0` (`x10`) — cursor at the first child item (absolute pointer); unchanged on
    the not-a-list path.
  * `a1` (`x11`) — `end = list_ptr + list_len` (exclusive).
  * `a2` (`x12`) — **status**: `0` ok / `1` not-a-list (prefix `< 0xc0`).

  Scratch `t0`,`t1`,`t2` (`x5`,`x6`,`x7`) clobbered; `ra` preserved.

  ## Verification status

  Lays out the 17-instruction body `rlp_walk_init_prog`. **All three cases** are
  proved (axiom-clean): `…_fail_spec_within` (prefix `< 0xc0`, status 1),
  `…_short_spec_within` (`0xc0 ≤ prefix < 0xf8`, status 0), `…_long_spec_within`
  (`prefix ≥ 0xf8`, status 0). The unified dispatch theorem `…_spec_within`
  combines them with static preconditions and a three-way postcondition
  disjunction (per `AGENTS.md`).
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
The verified drop-in body for the codegen guest `rlp_walk_init` (17 instructions).
Register map: `a0=x10`, `a1=x11`, `a2=x12`, `t0=x5`, `t1=x6`, `t2=x7`, `ra=x1`.

```
   0  ADD  x11 x10 x11   ; a1 = a0 + a1 (end = list_ptr + list_len)
   1  LBU  x5  x10 0     ; t0 = prefix byte
   2  LI   x6  0xc0
   3  BLTU x5  x6  48    ; if prefix < 0xc0 goto fail (idx 15, +48)
   4  LI   x6  0xf8
   5  BLTU x5  x6  28    ; if prefix < 0xf8 goto short (idx 12, +28)
   6  LI   x6  0xf7      ; long list
   7  SUB  x7  x5  x6    ; t2 = prefix - 0xf7 (lol)
   8  ADDI x7  x7  1     ; t2 = lol + 1 (prefix bytes)
   9  ADD  x10 x10 x7    ; a0 = list_ptr + (lol+1)
  10  LI   x12 0         ; a2 = 0 (ok)
  11  JALR x0  x1  0     ; ret
  12  ADDI x10 x10 1     ; short: a0 = list_ptr + 1
  13  LI   x12 0
  14  JALR x0  x1  0     ; ret
  15  LI   x12 1         ; fail: a2 = 1 (not-a-list)
  16  JALR x0  x1  0     ; ret
```
-/
def rlp_walk_init_prog : List Instr :=
  [ .BEQ .x11 .x0 (156 : BitVec 13),   -- 0  list_len == 0 → empty (idx 39)
    .ADD .x11 .x10 .x11,               -- 1  end = list_ptr + list_len
    .LBU .x5 .x10 0,                   -- 2  prefix
    .LI .x6 (0xc0 : Word),             -- 3
    .BLTU .x5 .x6 (148 : BitVec 13),   -- 4  prefix < 0xc0 → notlist (idx 41)
    .LI .x6 (0xf8 : Word),             -- 5
    .BLTU .x5 .x6 (100 : BitVec 13),   -- 6  prefix < 0xf8 → short (idx 31)
    .LI .x6 (0xf7 : Word),             -- 7  long: lol = prefix - 0xf7
    .SUB .x7 .x5 .x6,                  -- 8
    .ADDI .x28 .x7 (1 : BitVec 12),    -- 9  header size = 1 + lol
    .ADD .x29 .x10 .x28,               -- 10 cursor = list_ptr + 1 + lol
    .BLTU .x11 .x29 (136 : BitVec 13), -- 11 end < cursor → ltrunc (idx 45)
    .LBU .x30 .x10 1,                  -- 12 first length byte
    .BEQ .x30 .x0 (136 : BitVec 13),   -- 13 len[0] == 0 → llz (idx 47)
    .LI .x31 (0 : Word),               -- 14 acc
    .ADDI .x6 .x10 (1 : BitVec 12),    -- 15 ptr = list_ptr + 1
    .MV .x30 .x7,                      -- 16 count = lol
    .BEQ .x30 .x0 (28 : BitVec 13),    -- 17 loop head: count == 0 → ldone (idx 24)
    .SLLI .x31 .x31 (8 : BitVec 6),    -- 18
    .LBU .x28 .x6 0,                   -- 19
    .OR .x31 .x31 .x28,                -- 20
    .ADDI .x6 .x6 (1 : BitVec 12),     -- 21
    .ADDI .x30 .x30 (-1 : BitVec 12),  -- 22
    .JAL .x0 (-24 : BitVec 21),        -- 23 → idx 17
    .LI .x6 (56 : Word),               -- 24 ldone
    .BLTU .x31 .x6 (96 : BitVec 13),   -- 25 decoded < 56 → lmin (idx 49)
    .ADD .x6 .x29 .x31,                -- 26 content_end = cursor + decoded
    .BNE .x6 .x11 (96 : BitVec 13),    -- 27 content_end != end → lmism (idx 51)
    .MV .x10 .x29,                     -- 28 cursor = list_ptr + 1 + lol
    .LI .x12 (0 : Word),               -- 29
    .JALR .x0 .x1 0,                   -- 30
    .LI .x6 (0xc0 : Word),             -- 31 short
    .SUB .x7 .x5 .x6,                  -- 32 content_len = prefix - 0xc0
    .ADDI .x28 .x7 (1 : BitVec 12),    -- 33 1 + content_len
    .ADD .x29 .x10 .x28,               -- 34 content_end
    .BNE .x29 .x11 (32 : BitVec 13),   -- 35 content_end != end → smism (idx 43)
    .ADDI .x10 .x10 (1 : BitVec 12),   -- 36 cursor = list_ptr + 1
    .LI .x12 (0 : Word),               -- 37
    .JALR .x0 .x1 0,                   -- 38
    .LI .x12 (2 : Word),               -- 39 empty
    .JALR .x0 .x1 0,                   -- 40
    .LI .x12 (1 : Word),               -- 41 notlist
    .JALR .x0 .x1 0,                   -- 42
    .LI .x12 (3 : Word),               -- 43 smism (short length mismatch)
    .JALR .x0 .x1 0,                   -- 44
    .LI .x12 (4 : Word),               -- 45 ltrunc (long header truncated)
    .JALR .x0 .x1 0,                   -- 46
    .LI .x12 (5 : Word),               -- 47 llz (long length-field leading zero)
    .JALR .x0 .x1 0,                   -- 48
    .LI .x12 (6 : Word),               -- 49 lmin (long non-minimal)
    .JALR .x0 .x1 0,                   -- 50
    .LI .x12 (7 : Word),               -- 51 lmism (long length mismatch)
    .JALR .x0 .x1 0 ]                  -- 52

theorem rlp_walk_init_prog_length : rlp_walk_init_prog.length = 53 := rfl

abbrev rlp_walk_init_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_walk_init_prog

instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/-! ## Strict re-proof: per-case Hoare triples + unified -/

/-- **empty** (`list_len == 0`): status `a2 = 2`. (idx 0 BEQ taken → idx 39,40.) -/
theorem rlp_walk_init_empty_spec_within (base raVal a2Old : Word) :
    cpsTripleWithin 3 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal))
      ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (2 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
  have hbeq := beq_spec_gen_within .x11 .x0 (156 : BitVec 13) (0 : Word) (0 : Word) base
  rw [show base + signExtend13 (156 : BitVec 13) = base + 156 from by
        rw [show signExtend13 (156 : BitVec 13) = (156 : Word) from by decide]] at hbeq
  have hmono0 : ∀ a i, CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 0 base
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hA := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono0 (cpsBranchWithin_frameR
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hbeq))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
  have hLI := li_spec_gen_within .x12 a2Old (2 : Word) (base + 156) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 160)
  simp only [signExtend12_0] at hRet
  have hB0 : cpsTripleWithin 2 (base + 156) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) ((.x12 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI hRet
  have hB := cpsTripleWithin_frameR ((.x11 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree) hB0
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hA hB)

/-- Common prefix (idx 0..3): `BEQ` not-taken (`list_len ≠ 0`) ⨾ `ADD` end ⨾ `LBU`
    prefix ⨾ `LI 0xc0`. `base → base+16`. Leaves `x5 = prefix`, `x6 = 0xc0`,
    `x11 = end = list_ptr + list_len`. -/
theorem wi_prefix (base listBase listLen t0Old t1Old : Word) (listBytes : List (BitVec 8))
    (listOff : Nat) (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word)) :
    cpsTripleWithin 4 base (base + 16) (rlp_walk_init_code base)
      ((.x11 ↦ᵣ listLen) ** (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ t0Old) **
        (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xc0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) := by
  have hbeq := beq_spec_gen_within .x11 .x0 (156 : BitVec 13) listLen (0 : Word) base
  rw [show base + signExtend13 (156 : BitVec 13) = base + 156 from by
        rw [show signExtend13 (156 : BitVec 13) = (156 : Word) from by decide],
      show (base : Word) + 4 = base + 4 from rfl] at hbeq
  have hmono0 : ∀ a i, CodeReq.singleton base (.BEQ .x11 .x0 (156 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 0 base
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hA := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono0 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        bytesRegion listBase listBytes) (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hlen ((sepConj_pure_right _).1 h_pure).2)
  have hadd := add_spec_gen_rd_eq_rs2_within .x11 .x10 (listBase + BitVec.ofNat 64 listOff) listLen
    (base + 4) (by decide)
  have hlbu := bytesRegion_lbu_within .x5 .x10 listBase t0Old (base + 8) listBytes listOff
    (by decide) hsalign hoff hover hvalid
  have hLI := li_spec_gen_within .x6 t1Old (0xc0 : Word) (base + 12) (by decide)
  have hBlk : cpsTripleWithin 3 (base + 4) (base + 16) (rlp_walk_init_code base)
      ((.x11 ↦ᵣ listLen) ** (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ t0Old) **
        (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xc0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) := by
    runBlock hadd hlbu hLI
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hA hBlk
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) hseq

/-- **not-a-list** (`prefix < 0xc0`): status `a2 = 1`. (prefix ⨾ idx 4 BLTU taken → idx 41,42.) -/
theorem rlp_walk_init_notlist_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old : Word) (listBytes : List (BitVec 8))
    (listOff : Nat) (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_notlist : BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 7 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase listBytes) := by
  have hpre := cpsTripleWithin_frameR ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree)
    (wi_prefix base listBase listLen t0Old t1Old listBytes listOff hsalign hoff hover
      hvalid hlen)
  have hbltu := bltu_spec_gen_within .x5 .x6 (148 : BitVec 13)
    ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) (base + 16)
  rw [show (base + 16) + signExtend13 (148 : BitVec 13) = base + 164 from by
        rw [show signExtend13 (148 : BitVec 13) = (148 : Word) from by decide]; bv_omega] at hbltu
  have hmono4 : ∀ a i, CodeReq.singleton (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 4 (base + 16)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono4 (cpsBranchWithin_frameR
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_notlist)
  have hLI := li_spec_gen_within .x12 a2Old (1 : Word) (base + 164) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 168)
  simp only [signExtend12_0] at hRet
  have hfail : cpsTripleWithin 2 (base + 164) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) ((.x12 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI hRet
  have hfail' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xc0 : Word)) **
      (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
      (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase listBytes) (by pcFree) hfail
  have hs1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hpre hbr
  have hs2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hs1 hfail'
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) hs2
  have hp' := sepConj_mono_right (sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6) (fun _ x => x))) h hp
  xperm_hyp hp'

/-- Prefix + classify (idx 0..5): `wi_prefix` ⨾ idx 4 BLTU not-taken (`prefix ≥ 0xc0`)
    ⨾ idx 5 `LI x6 0xf8`. `base → base+24`. Leaves `x5 = prefix`, `x6 = 0xf8`. -/
theorem wi_to_f8 (base listBase listLen t0Old t1Old : Word) (listBytes : List (BitVec 8))
    (listOff : Nat) (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 6 base (base + 24) (rlp_walk_init_code base)
      ((.x11 ↦ᵣ listLen) ** (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ t0Old) **
        (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xf8 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) := by
  have hpre := wi_prefix base listBase listLen t0Old t1Old listBytes listOff hsalign hoff hover
    hvalid hlen
  have hbltu := bltu_spec_gen_within .x5 .x6 (148 : BitVec 13)
    ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) (base + 16)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hbltu
  have hmono4 : ∀ a i, CodeReq.singleton (base + 16) (.BLTU .x5 .x6 (148 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 4 (base + 16)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono4 (cpsBranchWithin_frameR
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes) (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_ge ((sepConj_pure_right _).1 h_pure).2)
  have hLI := li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 20) (by decide)
  have hLIblk : cpsTripleWithin 1 (base + 20) (base + 24) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes) := by
    runBlock hLI
  have hs1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hpre hbr
  have hs2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hs1 hLIblk
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) hs2

/-- **short list** (`0xc0 ≤ prefix < 0xf8`, EXACT `1 + (prefix-0xc0) = list_len`):
    cursor `= list_ptr + 1`, status `a2 = 0`. -/
theorem rlp_walk_init_short_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      = (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin 15 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  have hcls := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x1 ↦ᵣ raVal))
    (by pcFree)
    (wi_to_f8 base listBase listLen t0Old t1Old listBytes listOff hsalign hoff hover hvalid hlen
      h_ge)
  -- idx 6 BLTU x5 x6 100 TAKEN (prefix < 0xf8). base+24 → base+124.
  have hbltu := bltu_spec_gen_within .x5 .x6 (100 : BitVec 13) pfx (0xf8 : Word) (base + 24)
  rw [show (base + 24) + signExtend13 (100 : BitVec 13) = base + 124 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]; bv_omega] at hbltu
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 6 (base + 24)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono6 (cpsBranchWithin_frameR
      ((.x11 ↦ᵣ (ptr + listLen)) ** (.x10 ↦ᵣ ptr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) **
        (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase listBytes) (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_hi)
  -- short setup (idx 31..34): LI x6 0xc0 ; SUB x7 x5 x6 ; ADDI x28 x7 1 ; ADD x29 x10 x28.
  have hsLI := li_spec_gen_within .x6 (0xf8 : Word) (0xc0 : Word) (base + 124) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xc0 : Word) t2Old (base + 128) (by decide)
  have ha28 := addi_spec_gen_within .x28 .x7 t3Old (pfx - (0xc0 : Word)) (1 : BitVec 12) (base + 132)
    (by decide)
  have ha29 := add_spec_gen_within .x29 .x10 .x28 ptr ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
    t4Old (base + 136) (by decide)
  have hsetup : cpsTripleWithin 4 (base + 124) (base + 140) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x10 ↦ᵣ ptr) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xc0 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x10 ↦ᵣ ptr) **
        (.x29 ↦ᵣ (ptr + ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))))) := by
    runBlock hsLI hsub ha28 ha29
  have hsetup' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (ptr + listLen)) ** (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
      bytesRegion listBase listBytes) (by pcFree) hsetup
  -- idx 35 BNE x29 x11 32 NOT-taken (content_end = end). base+140 → base+144.
  have hbne := bne_spec_gen_within .x29 .x11
    (32 : BitVec 13) (ptr + ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) (ptr + listLen)
    (base + 140)
  rw [show (base + 140 : Word) + 4 = base + 144 from by bv_omega] at hbne
  have hmono35 : ∀ a i, CodeReq.singleton (base + 140) (.BNE .x29 .x11 (32 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 35 (base + 140)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbne' := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono35 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xc0 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x10 ↦ᵣ ptr) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      (by pcFree) hbne))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 (by rw [hptr] at h_exact ⊢; exact h_exact))
  -- return (idx 36..38): ADDI x10 x10 1 ; LI x12 0 ; ret. base+144 → ra.
  have ha10 := addi_spec_gen_same_within .x10 ptr (1 : BitVec 12) (base + 144) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 148) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 152)
  simp only [signExtend12_0] at hRet
  have hret : cpsTripleWithin 3 (base + 144) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ ptr) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ (ptr + signExtend12 (1 : BitVec 12))) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock ha10 hLI0 hRet
  have hret' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (ptr + listLen)) ** (.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0xc0 : Word)) **
      (.x7 ↦ᵣ (pfx - (0xc0 : Word))) **
      (.x28 ↦ᵣ ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) **
      (.x29 ↦ᵣ (ptr + ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)))) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hret
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcls hbr
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c1 hsetup'
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2 hbne'
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c3 hret'
  rw [show (6 + 1 + 4 + 1 + 3) = 15 from by norm_num] at c4
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c4
  have hp' := sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
        (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x))))))) h hp
  xperm_hyp hp'

end EvmAsm.Rv64.RLP
