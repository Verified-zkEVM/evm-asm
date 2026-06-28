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

/-- One iteration of the long-list length loop (idx 18..22), `base+72 → base+92`.
    acc=`x31`, ptr=`x6`, byte=`x28`, count=`x30`. -/
theorem wi_len_body (base srcBase x31Old x28Old x30Val : Word) (srcBytes : List (BitVec 8))
    (si : Nat) (hsalign : srcBase.toNat % 8 = 0) (hsi : si < srcBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true) :
    cpsTripleWithin 5 (base + 72) (base + 92) (rlp_walk_init_code base)
      ((.x31 ↦ᵣ x31Old) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x28 ↦ᵣ x28Old) **
       (.x30 ↦ᵣ x30Val) ** bytesRegion srcBase srcBytes)
      ((.x31 ↦ᵣ ((x31Old <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi))) **
       (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi)) **
       (.x30 ↦ᵣ (x30Val + signExtend12 (-1 : BitVec 12))) ** bytesRegion srcBase srcBytes) := by
  have hslli := slli_spec_gen_same_within .x31 x31Old (8 : BitVec 6) (base + 72) (by nofun)
  rw [show (8 : BitVec 6).toNat = 8 from by decide] at hslli
  have hlbu := bytesRegion_lbu_within .x28 .x6 srcBase x28Old (base + 76) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have hor := or_spec_gen_rd_eq_rs1_within .x31 .x28 (x31Old <<< (8 : Nat))
    (BitVec.setWidth 64 (srcBytes[si]'hsi)) (base + 80) (by nofun)
  have ha6 := addi_spec_gen_same_within .x6 (srcBase + BitVec.ofNat 64 si) 1 (base + 84) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha6
  have ha30 := addi_spec_gen_same_within .x30 x30Val (-1 : BitVec 12) (base + 88) (by nofun)
  runBlock hslli hlbu hor ha6 ha30

set_option maxRecDepth 8000 in
/-- The long-list length loop (idx 17..23), `base+68 → base+96`, by induction on the
    counter `x30`; accumulates `x31 = fromBytesBE` of the read length bytes. -/
theorem wi_len_loop (base srcBase x28Old : Word) (srcBytes pre : List (BitVec 8)) (si n : Nat)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hbound : pre.length + n ≤ 8)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 68) (base + 96) (rlp_walk_init_code base)
      ((.x30 ↦ᵣ BitVec.ofNat 64 n) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x28 ↦ᵣ x28Old) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))) **
       regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 68) (.BEQ .x30 .x0 (28 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 17 (base + 68)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have ha_t : (base + 68) + signExtend13 (28 : BitVec 13) = base + 96 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 68 : Word) + 4 = base + 72 := by bv_omega
  induction n generalizing si pre x28Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x30 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word) (base + 68)
    rw [ha_t, ha_f] at hbeq
    have htaken := cpsBranchWithin_takenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x28 ↦ᵣ x28Old) **
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
    have hbeq := beq_spec_gen_within .x30 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1)) (0 : Word) (base + 68)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x28 ↦ᵣ x28Old) **
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
    have body := wi_len_body base srcBase (BitVec.ofNat 64 (Nat.fromBytesBE pre)) x28Old
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
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 92)
    have ha_back : (base + 92) + signExtend21 (-24 : BitVec 21) = base + 68 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 92) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_walk_init_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 23 (base + 92)
        (by rw [rlp_walk_init_prog_length]; norm_num)
        (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 92) (base + 68) (rlp_walk_init_code base)
        ((.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x30 ↦ᵣ BitVec.ofNat 64 k) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
        ((.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x30 ↦ᵣ BitVec.ofNat 64 k) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x28 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
           (.x30 ↦ᵣ BitVec.ofNat 64 k) ** (.x6 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
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

end EvmAsm.Rv64.RLP
