/-
  EvmAsm.Rv64.RLP.WalkInit

  A verified RISC-V leaf subroutine: a CPS drop-in for the codegen guest function
  `rlp_walk_init` emitted by `EvmAsm/Codegen/Programs/RlpWalk.lean`
  (`rlpWalkInitFunction`, added in #9503's cursor-walk RLP decode work).

  `rlp_walk_init` skips the outer RLP **list** prefix (`0xc0..0xff`) so the cursor
  points at the first encoded child item. This is the **strict** (EXACT, structural
  -canonicality-enforcing) drop-in: it reads the long-list length field, requires the
  header + content to *exactly* fill `list_len`, and rejects non-canonical framing —
  mirroring Python execution-specs (`ethereum_rlp/rlp.py`). It decodes no scalar, so the
  scalar-canonicality rule (`ContentToU256Be`/`ContentToU64`) does not apply here.

  ## Caller-facing contract (LP64)

  Frameless leaf: reached by `jal ra, rlp_walk_init`, returns via `ret`.

  ### Inputs
  * `a0` (`x10`) — list bytes pointer (start of the outer list prefix).
  * `a1` (`x11`) — total list byte length (the EXACT full encoded item span).

  ### Outputs
  * `a0` (`x10`) — cursor at the first child item (absolute pointer); unchanged on
    every failure path.
  * `a1` (`x11`) — `end = list_ptr + list_len` (exclusive).
  * `a2` (`x12`) — **status** (distinct code per failure reason, for debugging):
    `0` ok · `1` not-a-list (`prefix < 0xc0`) · `2` empty (`list_len = 0`) ·
    `3` short length mismatch · `4` long header truncated · `5` long length-field
    leading zero · `6` long non-minimal (`< 56`) · `7` long length mismatch.

  Scratch `t0..t6` (`x5`,`x6`,`x7`,`x28..x31`) clobbered; `ra` preserved.

  ## Verification status

  Lays out the strict 53-instruction body `rlp_walk_init_prog`. **All nine outcomes**
  are proved axiom-clean: `…_empty/…_notlist/…_short/…_smism/…_ltrunc/…_llz/…_lmin/
  …_lmism/…_long_spec_within`. The long path's length-field accumulation is verified by
  `wi_len_loop` (reusing `cu64_step`/`fromBytesBE`). The unified dispatch theorem
  `rlp_walk_init_spec_within` combines all nine with static preconditions (the long-list
  length-field validity assumed only when `prefix ≥ 0xf8`) and a nine-way postcondition
  disjunction (`≤ 81` steps), per `AGENTS.md`.
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
    .ADDI .x6 .x10 (1 : BitVec 12),    -- 12 ptr = list_ptr + 1 (length-field ptr)
    .LBU .x30 .x6 0,                   -- 13 first length byte (at ptr+1)
    .BEQ .x30 .x0 (132 : BitVec 13),   -- 14 len[0] == 0 → llz (idx 47)
    .LI .x31 (0 : Word),               -- 15 acc
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

/-- Long-list setup (idx 0..10): `wi_to_f8` ⨾ idx6 BLTU-nt (`prefix ≥ 0xf8`) ⨾
    `LI x6 0xf7` ⨾ `SUB x7` (lol) ⨾ `ADDI x28` (1+lol) ⨾ `ADD x29` (cursor).
    `base → base+44`. -/
theorem wi_long_setup (base listBase listLen t0Old t1Old t2Old t3Old t4Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true) :
    cpsTripleWithin 11 base (base + 44) (rlp_walk_init_code base)
      ((.x11 ↦ᵣ listLen) ** (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ t0Old) **
        (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xf7 : Word)) **
        (.x7 ↦ᵣ ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word))) **
        (.x28 ↦ᵣ (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
        (.x29 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
          (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  have hcls := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old)) (by pcFree)
    (wi_to_f8 base listBase listLen t0Old t1Old listBytes listOff hsalign hoff hover hvalid hlen h_ge)
  have hbltu := bltu_spec_gen_within .x5 .x6 (100 : BitVec 13) pfx (0xf8 : Word) (base + 24)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbltu
  have hmono6 : ∀ a i, CodeReq.singleton (base + 24) (.BLTU .x5 .x6 (100 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 6 (base + 24)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono6 (cpsBranchWithin_frameR
      ((.x11 ↦ᵣ (ptr + listLen)) ** (.x10 ↦ᵣ ptr) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hbltu))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_ge_f8 ((sepConj_pure_right _).1 h_pure).2)
  have hLI7 := li_spec_gen_within .x6 (0xf8 : Word) (0xf7 : Word) (base + 28) (by decide)
  have hsub := sub_spec_gen_within .x7 .x5 .x6 pfx (0xf7 : Word) t2Old (base + 32) (by decide)
  have ha28 := addi_spec_gen_within .x28 .x7 t3Old (pfx - (0xf7 : Word)) (1 : BitVec 12) (base + 36)
    (by decide)
  have ha29 := add_spec_gen_within .x29 .x10 .x28 ptr
    ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) t4Old (base + 40) (by decide)
  have hsetup : cpsTripleWithin 4 (base + 28) (base + 44) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (0xf8 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x10 ↦ᵣ ptr) ** (.x29 ↦ᵣ t4Old))
      ((.x6 ↦ᵣ (0xf7 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x10 ↦ᵣ ptr) **
        (.x29 ↦ᵣ (ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))))) := by
    runBlock hLI7 hsub ha28 ha29
  have hsetup' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (ptr + listLen)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
    (by pcFree) hsetup
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcls hbr
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c1 hsetup'
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) c2

/-- **long list** (`prefix ≥ 0xf8`, EXACT). `lol = prefix - 0xf7` length bytes,
    `dec = fromBytesBE` of them; header fits, `len[0] ≠ 0`, `dec ≥ 56`, `cursor + dec = end`
    ⇒ cursor `= list_ptr + 1 + lol`, status `a2 = 0`. -/
theorem rlp_walk_init_long_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ listBytes.length)
    (hlover : listBase.toNat + (listOff + 1 +
      ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1 + k)) = true)
    (hoff1 : listOff + 1 < listBytes.length)
    (h_fits : ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
      ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) = true)
    (h_llz : (listBytes[listOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
      ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_match : ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
      = (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin (7 * ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 25) base
        (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
          (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  set lol : Nat := (pfx - (0xf7 : Word)).toNat with hlol
  have hlol8 : lol ≤ 8 := by
    rw [hlol]
    simp only [BitVec.ult, decide_eq_true_eq, show (0xf8 : Word).toNat = 248 from by decide] at h_ge_f8
    have hpb : pfx.toNat < 256 := by
      rw [hpfx]; simp only [BitVec.toNat_setWidth]; have := (listBytes[listOff]'hoff).isLt; omega
    rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hlol1 : 1 ≤ lol := by
    rw [hlol]
    simp only [BitVec.ult, decide_eq_true_eq, show (0xf8 : Word).toNat = 248 from by decide] at h_ge_f8
    have hpb : pfx.toNat < 256 := by
      rw [hpfx]; simp only [BitVec.toNat_setWidth]; have := (listBytes[listOff]'hoff).isLt; omega
    rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  have hxn : pfx - (0xf7 : Word) = BitVec.ofNat 64 lol := by
    rw [hlol, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hp1eq : ptr + (1 : Word) = listBase + BitVec.ofNat 64 (listOff + 1) := by
    rw [hptr]; bv_omega
  set dec : Word := BitVec.ofNat 64
    (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take lol)) with hdec
  set cur : Word := ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) with hcur
  have hsetup := cpsTripleWithin_frameR ((.x12 ↦ᵣ a2Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      (.x1 ↦ᵣ raVal)) (by pcFree)
    (wi_long_setup base listBase listLen t0Old t1Old t2Old t3Old t4Old listBytes listOff hsalign hoff
      hover hvalid hlen h_ge h_ge_f8)
  have hbltu11 := bltu_spec_gen_within .x11 .x29 (136 : BitVec 13) (ptr + listLen) cur (base + 44)
  rw [show (base + 44 : Word) + 4 = base + 48 from by bv_addr] at hbltu11
  have hmono11 : ∀ a i, CodeReq.singleton (base + 44) (.BLTU .x11 .x29 (136 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 11 (base + 44)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr11 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono11 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0xf7 : Word)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x12 ↦ᵣ a2Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes) (by pcFree) hbltu11))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fits (by rw [hptr, hcur]; exact ((sepConj_pure_right _).1 h_pure).2))
  have ha6 := addi_spec_gen_within .x6 .x10 (0xf7 : Word) ptr (1 : BitVec 12) (base + 48) (by decide)
  rw [show ptr + signExtend12 (1 : BitVec 12) = listBase + BitVec.ofNat 64 (listOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide, hp1eq]] at ha6
  have ha6blk : cpsTripleWithin 1 (base + 48) (base + 52) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (0xf7 : Word)) ** (.x10 ↦ᵣ ptr))
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** (.x10 ↦ᵣ ptr)) := by runBlock ha6
  have hlbu := bytesRegion_lbu_within .x30 .x6 listBase t5Old (base + 52) listBytes (listOff + 1)
    (by decide) hsalign hoff1 (by omega) (by have := hlvalid 0 (by omega); simpa using this)
  have hlbublk : cpsTripleWithin 1 (base + 52) (base + 56) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** (.x30 ↦ᵣ t5Old) **
        bytesRegion listBase listBytes)
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) **
        (.x30 ↦ᵣ (listBytes[listOff + 1]'hoff1).zeroExtend 64) ** bytesRegion listBase listBytes) := by
    runBlock hlbu
  have hbeq := beq_spec_gen_within .x30 .x0 (132 : BitVec 13)
    ((listBytes[listOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_addr] at hbeq
  have hmono14 : ∀ a i, CodeReq.singleton (base + 56) (.BEQ .x30 .x0 (132 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 14 (base + 56)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr14 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono14 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** bytesRegion listBase listBytes)
      (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_llz ((sepConj_pure_right _).1 h_pure).2)
  have hLIacc := li_spec_gen_within .x31 t6Old (0 : Word) (base + 60) (by decide)
  have hmv := mv_spec_gen_within .x30 .x7 (pfx - (0xf7 : Word))
    ((listBytes[listOff + 1]'hoff1).zeroExtend 64) (base + 64) (by decide)
  have hsetup2 : cpsTripleWithin 2 (base + 60) (base + 68) (rlp_walk_init_code base)
      ((.x31 ↦ᵣ t6Old) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x30 ↦ᵣ (listBytes[listOff + 1]'hoff1).zeroExtend 64))
      ((.x31 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x30 ↦ᵣ (pfx - (0xf7 : Word)))) := by runBlock hLIacc hmv
  have hloop := wi_len_loop base listBase ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))
    listBytes [] (listOff + 1) lol hsalign (by rw [hlol] at hllen ⊢; exact hllen)
    (by rw [hlol] at hlover ⊢; exact hlover) (by simp; omega)
    (by intro k hk; exact hlvalid k (by rw [hlol] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hxn] at hloop
  have hLI56 := li_spec_gen_within .x6 (listBase + BitVec.ofNat 64 (listOff + 1 + lol)) (56 : Word)
    (base + 96) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 96) (base + 100) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1 + lol)))) ((.x6 ↦ᵣ (56 : Word))) := by
    runBlock hLI56
  have hbltu25 := bltu_spec_gen_within .x31 .x6 (96 : BitVec 13) dec (56 : Word) (base + 100)
  rw [show (base + 100 : Word) + 4 = base + 104 from by bv_addr] at hbltu25
  have hmono25 : ∀ a i, CodeReq.singleton (base + 100) (.BLTU .x31 .x6 (96 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 25 (base + 100)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr25 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono25 hbltu25)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hr⟩ := hQt
      exact h_min ((sepConj_pure_right _).1 hr).2)
  -- idx 26 ADD x6 x29 x31 (content_end = cursor + dec).  base+104 → base+108.
  have hadd26 := add_spec_gen_within .x6 .x29 .x31 cur dec (56 : Word) (base + 104) (by decide)
  have hadd26blk : cpsTripleWithin 1 (base + 104) (base + 108) (rlp_walk_init_code base)
      ((.x29 ↦ᵣ cur) ** (.x31 ↦ᵣ dec) ** (.x6 ↦ᵣ (56 : Word)))
      ((.x29 ↦ᵣ cur) ** (.x31 ↦ᵣ dec) ** (.x6 ↦ᵣ (cur + dec))) := by runBlock hadd26
  -- idx 27 BNE x6 x11 96 NOT-taken (content_end = end).  base+108 → base+112.
  have hbne27 := bne_spec_gen_within .x6 .x11 (96 : BitVec 13) (cur + dec) (ptr + listLen) (base + 108)
  rw [show (base + 108 : Word) + 4 = base + 112 from by bv_addr] at hbne27
  have hmono27 : ∀ a i, CodeReq.singleton (base + 108) (.BNE .x6 .x11 (96 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 27 (base + 108)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr27 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono27 hbne27)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hr⟩ := hQt
      exact ((sepConj_pure_right _).1 hr).2 h_match)
  -- idx 28..30: MV x10 x29 ; LI x12 0 ; ret.  base+112 → ra.
  have hmv28 := mv_spec_gen_within .x10 .x29 cur ptr (base + 112) (by decide)
  have hLI0 := li_spec_gen_within .x12 a2Old (0 : Word) (base + 116) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 120)
  simp only [signExtend12_0] at hRet
  have hretblk : cpsTripleWithin 3 (base + 112) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ ptr) ** (.x29 ↦ᵣ cur) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x10 ↦ᵣ cur) ** (.x29 ↦ᵣ cur) ** (.x12 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hmv28 hLI0 hRet
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsetup hbr11
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c1 (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x11 ↦ᵣ (ptr + listLen)) **
         (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
         (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) ha6blk)
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
       (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
       (.x29 ↦ᵣ cur) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hlbublk)
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c3
    (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
         (.x12 ↦ᵣ a2Old) ** (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
         (.x29 ↦ᵣ cur) ** (.x31 ↦ᵣ t6Old) ** (.x1 ↦ᵣ raVal)) (by pcFree) hbr14)
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1))) h hp
      xperm_hyp hp2) c4
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** (.x10 ↦ᵣ ptr) **
       (.x11 ↦ᵣ (ptr + listLen)) ** (.x12 ↦ᵣ a2Old) **
       (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ cur) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) hsetup2)
  have hloop' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
     (.x12 ↦ᵣ a2Old) ** (.x29 ↦ᵣ cur) ** (.x1 ↦ᵣ raVal)) (by pcFree) hloop
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c5 hloop'
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c6
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
       (.x12 ↦ᵣ a2Old) ** (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ dec) ** regOwn .x28 **
       (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) hLI56blk)
  have c8 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c7
    (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
         (.x12 ↦ᵣ a2Old) ** (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ (0 : Word)) ** regOwn .x28 **
         (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) hbr25)
  have c9 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c8
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
       (.x12 ↦ᵣ a2Old) ** (.x30 ↦ᵣ (0 : Word)) ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
       (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) hadd26blk)
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c9
    (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x12 ↦ᵣ a2Old) **
         (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ dec) ** regOwn .x28 **
         (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) hbr27)
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c10
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (cur + dec)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
       (.x11 ↦ᵣ (ptr + listLen)) ** (.x30 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ dec) ** regOwn .x28 **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hretblk)
  rw [show (11 + 1 + 1 + 1 + 1 + 2 + (7 * lol + 1) + 1 + 1 + 1 + 1 + 3) = 7 * lol + 25 from by ring]
    at c11
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c11
  have hp' := sepConj_mono_left
    (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x29) (fun _ x => x))) h hp
  have hp'' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (regIs_implies_regOwn .x31)
          (fun _ x => x))))))) h hp'
  xperm_hyp hp''

/-- **long header truncated** (`prefix ≥ 0xf8`, `end < cursor`): status `a2 = 4`.
    (wi_long_setup ⨾ idx 11 BLTU taken → idx 45,46.) -/
theorem rlp_walk_init_ltrunc_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_trunc : BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
      ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
      = true) :
    cpsTripleWithin 14 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (4 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  set cur : Word := ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) with hcur
  have hsetup := cpsTripleWithin_frameR ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree)
    (wi_long_setup base listBase listLen t0Old t1Old t2Old t3Old t4Old listBytes listOff hsalign hoff
      hover hvalid hlen h_ge h_ge_f8)
  have hbltu11 := bltu_spec_gen_within .x11 .x29 (136 : BitVec 13) (ptr + listLen) cur (base + 44)
  rw [show (base + 44 : Word) + signExtend13 (136 : BitVec 13) = base + 180 from by
        rw [show signExtend13 (136 : BitVec 13) = (136 : Word) from by decide]; bv_omega] at hbltu11
  have hmono11 : ∀ a i, CodeReq.singleton (base + 44) (.BLTU .x11 .x29 (136 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 11 (base + 44)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono11 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0xf7 : Word)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hbltu11))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by rw [hptr, hcur]; exact h_trunc))
  have hLI := li_spec_gen_within .x12 a2Old (4 : Word) (base + 180) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 184)
  simp only [signExtend12_0] at hRet
  have hfail : cpsTripleWithin 2 (base + 180) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) ((.x12 ↦ᵣ (4 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI hRet
  have hfail' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (ptr + listLen)) ** (.x29 ↦ᵣ cur) ** (.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ pfx) **
      (.x6 ↦ᵣ (0xf7 : Word)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase listBytes) (by pcFree) hfail
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsetup hbr
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) s1 hfail'
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s2
  have hp' := sepConj_mono_right
    (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x29)
      (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x5)
        (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
          (sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x)))))))) h hp
  xperm_hyp hp'

/-- Long path through the first-length-byte read (idx 0..13): `wi_long_setup` ⨾ idx 11
    BLTU not-taken (`cursor ≤ end`) ⨾ idx 12 `ADDI x6 x10 1` ⨾ idx 13 `LBU x30 x6 0`.
    `base → base+56`. Leaves `x6 = ptr+1`, `x29 = cursor`, `x30 = len[0]`. -/
theorem wi_long_to_lbu (base listBase listLen t0Old t1Old t2Old t3Old t4Old t5Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hoff1 : listOff + 1 < listBytes.length) (hover1 : listBase.toNat + (listOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1)) = true)
    (h_fits : ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
      ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
      = true) :
    cpsTripleWithin 14 base (base + 56) (rlp_walk_init_code base)
      ((.x11 ↦ᵣ listLen) ** (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ t0Old) **
        (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) **
        (.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) **
        (.x7 ↦ᵣ ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word))) **
        (.x28 ↦ᵣ (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
        (.x29 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
          (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x30 ↦ᵣ (listBytes[listOff + 1]'hoff1).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  set cur : Word := ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) with hcur
  have hp1eq : ptr + (1 : Word) = listBase + BitVec.ofNat 64 (listOff + 1) := by rw [hptr]; bv_omega
  have hsetup := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old)) (by pcFree)
    (wi_long_setup base listBase listLen t0Old t1Old t2Old t3Old t4Old listBytes listOff hsalign hoff
      hover hvalid hlen h_ge h_ge_f8)
  have hbltu11 := bltu_spec_gen_within .x11 .x29 (136 : BitVec 13) (ptr + listLen) cur (base + 44)
  rw [show (base + 44 : Word) + 4 = base + 48 from by bv_addr] at hbltu11
  have hmono11 : ∀ a i, CodeReq.singleton (base + 44) (.BLTU .x11 .x29 (136 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 11 (base + 44)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr11 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono11 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (0xf7 : Word)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x30 ↦ᵣ t5Old) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hbltu11))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_fits ((sepConj_pure_right _).1 h_pure).2)
  have ha6 := addi_spec_gen_within .x6 .x10 (0xf7 : Word) ptr (1 : BitVec 12) (base + 48) (by decide)
  rw [show ptr + signExtend12 (1 : BitVec 12) = listBase + BitVec.ofNat 64 (listOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide, hp1eq]] at ha6
  have ha6blk : cpsTripleWithin 1 (base + 48) (base + 52) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (0xf7 : Word)) ** (.x10 ↦ᵣ ptr))
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** (.x10 ↦ᵣ ptr)) := by runBlock ha6
  have hlbu := bytesRegion_lbu_within .x30 .x6 listBase t5Old (base + 52) listBytes (listOff + 1)
    (by decide) hsalign hoff1 hover1 hvalid1
  have hlbublk : cpsTripleWithin 1 (base + 52) (base + 56) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** (.x30 ↦ᵣ t5Old) **
        bytesRegion listBase listBytes)
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) **
        (.x30 ↦ᵣ (listBytes[listOff + 1]'hoff1).zeroExtend 64) ** bytesRegion listBase listBytes) := by
    runBlock hlbu
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hsetup hbr11
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c1 (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x11 ↦ᵣ (ptr + listLen)) **
         (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ cur) **
         (.x30 ↦ᵣ t5Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) ha6blk)
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
       (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ cur) **
       (.x0 ↦ᵣ (0 : Word))) (by pcFree) hlbublk)
  rw [show (11 + 1 + 1 + 1) = 14 from by norm_num] at c3
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) c3

/-- **long length-field leading zero** (`prefix ≥ 0xf8`, `len[0] = 0`): status `a2 = 5`.
    (wi_long_to_lbu ⨾ idx 14 BEQ taken → idx 47,48.) -/
theorem rlp_walk_init_llz_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hoff1 : listOff + 1 < listBytes.length) (hover1 : listBase.toNat + (listOff + 1) < 2 ^ 64)
    (hvalid1 : isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1)) = true)
    (h_fits : ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
      ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
      = true)
    (h_llz : (listBytes[listOff + 1]'hoff1).zeroExtend 64 = (0 : Word)) :
    cpsTripleWithin 17 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (5 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  have hpre := cpsTripleWithin_frameR ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree)
    (wi_long_to_lbu base listBase listLen t0Old t1Old t2Old t3Old t4Old t5Old listBytes listOff
      hsalign hoff hover hvalid hlen h_ge h_ge_f8 hoff1 hover1 hvalid1 h_fits)
  have hbeq := beq_spec_gen_within .x30 .x0 (132 : BitVec 13)
    ((listBytes[listOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 56)
  rw [show (base + 56) + signExtend13 (132 : BitVec 13) = base + 188 from by
        rw [show signExtend13 (132 : BitVec 13) = (132 : Word) from by decide]; bv_omega] at hbeq
  have hmono14 : ∀ a i, CodeReq.singleton (base + 56) (.BEQ .x30 .x0 (132 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 14 (base + 56)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono14 (cpsBranchWithin_frameR
      ((.x11 ↦ᵣ (ptr + listLen)) ** (.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ pfx) **
        (.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
        (.x29 ↦ᵣ (ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) ** (.x12 ↦ᵣ a2Old) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) (by pcFree) hbeq))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 h_llz)
  have hLI := li_spec_gen_within .x12 a2Old (5 : Word) (base + 188) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 192)
  simp only [signExtend12_0] at hRet
  have hfail : cpsTripleWithin 2 (base + 188) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) ((.x12 ↦ᵣ (5 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI hRet
  have hfail' := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ (listBytes[listOff + 1]'hoff1).zeroExtend 64) ** (.x11 ↦ᵣ (ptr + listLen)) **
      (.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) **
      (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
      (.x29 ↦ᵣ (ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hfail
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hpre hbr
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) s1 hfail'
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s2
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x30) (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x5)
        (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x7)
          (sepConj_mono (regIs_implies_regOwn .x28) (sepConj_mono (regIs_implies_regOwn .x29)
            (fun _ x => x))))))))) h hp
  xperm_hyp hp'

/-- Long path through the length loop (idx 0..23): `wi_long_to_lbu` ⨾ idx 14 BEQ not-taken
    (`len[0] ≠ 0`) ⨾ idx 15-16 (acc=0, count=lol) ⨾ length loop. `base → base+96`.
    Leaves `x31 = dec = fromBytesBE` of the length bytes, `x29 = cursor`. -/
theorem wi_long_to_dec (base listBase listLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ listBytes.length)
    (hlover : listBase.toNat + (listOff + 1 +
      ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1 + k)) = true)
    (hoff1 : listOff + 1 < listBytes.length)
    (h_fits : ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
      ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
      = true)
    (h_llz_ne : (listBytes[listOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word)) :
    cpsTripleWithin (7 * ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 18) base
        (base + 96) (rlp_walk_init_code base)
      ((.x11 ↦ᵣ listLen) ** (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x5 ↦ᵣ t0Old) **
        (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) **
        (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      ((.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) **
        (.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1 +
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) **
        (.x7 ↦ᵣ ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word))) ** regOwn .x28 **
        (.x29 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
          (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
        (.x30 ↦ᵣ (0 : Word)) **
        (.x31 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  set lol : Nat := (pfx - (0xf7 : Word)).toNat with hlol
  set cur : Word := ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) with hcur
  have hxn : pfx - (0xf7 : Word) = BitVec.ofNat 64 lol := by
    rw [hlol, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbnds : 1 ≤ lol ∧ lol ≤ 8 := by
    rw [hlol]
    simp only [BitVec.ult, decide_eq_true_eq, show (0xf8 : Word).toNat = 248 from by decide] at h_ge_f8
    have hpb : pfx.toNat < 256 := by
      rw [hpfx]; simp only [BitVec.toNat_setWidth]; have := (listBytes[listOff]'hoff).isLt; omega
    rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
  obtain ⟨hlol1, hlol8⟩ := hbnds
  have hpre := cpsTripleWithin_frameR ((.x31 ↦ᵣ t6Old)) (by pcFree)
    (wi_long_to_lbu base listBase listLen t0Old t1Old t2Old t3Old t4Old t5Old listBytes listOff
      hsalign hoff hover hvalid hlen h_ge h_ge_f8 hoff1 (by omega)
      (by have := hlvalid 0 (by omega); simpa using this) h_fits)
  have hbeq := beq_spec_gen_within .x30 .x0 (132 : BitVec 13)
    ((listBytes[listOff + 1]'hoff1).zeroExtend 64) (0 : Word) (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_addr] at hbeq
  have hmono14 : ∀ a i, CodeReq.singleton (base + 56) (.BEQ .x30 .x0 (132 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 14 (base + 56)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr14 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono14 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** bytesRegion listBase listBytes)
      (by pcFree) hbeq))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact h_llz_ne ((sepConj_pure_right _).1 h_pure).2)
  have hLIacc := li_spec_gen_within .x31 t6Old (0 : Word) (base + 60) (by decide)
  have hmv := mv_spec_gen_within .x30 .x7 (pfx - (0xf7 : Word))
    ((listBytes[listOff + 1]'hoff1).zeroExtend 64) (base + 64) (by decide)
  have hsetup2 : cpsTripleWithin 2 (base + 60) (base + 68) (rlp_walk_init_code base)
      ((.x31 ↦ᵣ t6Old) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x30 ↦ᵣ (listBytes[listOff + 1]'hoff1).zeroExtend 64))
      ((.x31 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
        (.x30 ↦ᵣ (pfx - (0xf7 : Word)))) := by runBlock hLIacc hmv
  have hloop := wi_len_loop base listBase ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))
    listBytes [] (listOff + 1) lol hsalign (by rw [hlol] at hllen ⊢; exact hllen)
    (by rw [hlol] at hlover ⊢; exact hlover)
    (by simp only [List.length_nil, Nat.zero_add]; omega)
    (by intro k hk; exact hlvalid k (by rw [hlol] at hk; exact hk))
  rw [show BitVec.ofNat 64 (Nat.fromBytesBE ([] : List (BitVec 8))) = (0 : Word) from rfl,
    List.nil_append, ← hxn] at hloop
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hpre
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
       (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x29 ↦ᵣ cur) **
       (.x31 ↦ᵣ t6Old)) (by pcFree) hbr14)
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1))) h hp
      xperm_hyp hp2) c1 (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx) ** (.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1))) ** (.x10 ↦ᵣ ptr) **
         (.x11 ↦ᵣ (ptr + listLen)) ** (.x28 ↦ᵣ ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) **
         (.x29 ↦ᵣ cur) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hsetup2)
  have hloop' := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
     (.x29 ↦ᵣ cur)) (by pcFree) hloop
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2 hloop'
  rw [show (14 + 1 + 2 + (7 * lol + 1)) = 7 * lol + 18 from by ring] at c3
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) c3

/-- **long non-minimal** (`prefix ≥ 0xf8`, `decoded < 56`): status `a2 = 6`.
    (wi_long_to_dec ⨾ idx 24 LI 56 ⨾ idx 25 BLTU taken → idx 49,50.) -/
theorem rlp_walk_init_lmin_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ listBytes.length)
    (hlover : listBase.toNat + (listOff + 1 +
      ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1 + k)) = true)
    (hoff1 : listOff + 1 < listBytes.length)
    (h_fits : ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
      ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
      = true)
    (h_llz_ne : (listBytes[listOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_lmin : BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
      ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true) :
    cpsTripleWithin (7 * ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 22) base
        (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (6 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  set lol : Nat := (pfx - (0xf7 : Word)).toNat with hlol
  set dec : Word := BitVec.ofNat 64
    (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take lol)) with hdec
  set cur : Word := ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) with hcur
  have hpre := cpsTripleWithin_frameR ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree)
    (wi_long_to_dec base listBase listLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBytes listOff
      hsalign hoff hover hvalid hlen h_ge h_ge_f8 hllen hlover hlvalid hoff1 h_fits h_llz_ne)
  have hLI56 := li_spec_gen_within .x6 (listBase + BitVec.ofNat 64 (listOff + 1 + lol)) (56 : Word)
    (base + 96) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 96) (base + 100) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1 + lol)))) ((.x6 ↦ᵣ (56 : Word))) := by
    runBlock hLI56
  have hbltu25 := bltu_spec_gen_within .x31 .x6 (96 : BitVec 13) dec (56 : Word) (base + 100)
  rw [show (base + 100) + signExtend13 (96 : BitVec 13) = base + 196 from by
        rw [show signExtend13 (96 : BitVec 13) = (96 : Word) from by decide]; bv_omega] at hbltu25
  have hmono25 : ∀ a i, CodeReq.singleton (base + 100) (.BLTU .x31 .x6 (96 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 25 (base + 100)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono25 hbltu25)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hr⟩ := hQf
      exact ((sepConj_pure_right _).1 hr).2 h_lmin)
  have hLI := li_spec_gen_within .x12 a2Old (6 : Word) (base + 196) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 200)
  simp only [signExtend12_0] at hRet
  have hfail : cpsTripleWithin 2 (base + 196) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) ((.x12 ↦ᵣ (6 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI hRet
  have hfail' := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ dec) ** (.x6 ↦ᵣ (56 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) **
      (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) ** regOwn .x28 ** (.x29 ↦ᵣ cur) **
      (.x30 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hfail
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hpre
    (cpsTripleWithin_frameR
      ((.x31 ↦ᵣ dec) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) **
       (.x11 ↦ᵣ (ptr + listLen)) ** regOwn .x28 ** (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      (by pcFree) hLI56blk)
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
       regOwn .x28 ** (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hbr)
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) s2 hfail'
  rw [show (7 * lol + 18 + 1 + 1 + 2) = 7 * lol + 22 from by ring] at s3
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s3
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x31) (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x7)
        (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x29)
            (sepConj_mono (regIs_implies_regOwn .x30) (fun _ x => x)))))))))) h hp
  xperm_hyp hp'

/-- **long length mismatch** (`prefix ≥ 0xf8`, `decoded ≥ 56`, `cursor + decoded ≠ end`):
    status `a2 = 7`. (wi_long_to_dec ⨾ idx 25 BLTU nt ⨾ idx 26 ADD ⨾ idx 27 BNE taken → idx 51,52.) -/
theorem rlp_walk_init_lmism_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_ge_f8 : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (hllen : listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
      ≤ listBytes.length)
    (hlover : listBase.toNat + (listOff + 1 +
      ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hlvalid : ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
      isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1 + k)) = true)
    (hoff1 : listOff + 1 < listBytes.length)
    (h_fits : ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
      ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
      = true)
    (h_llz_ne : (listBytes[listOff + 1]'hoff1).zeroExtend 64 ≠ (0 : Word))
    (h_min : ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
      ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true)
    (h_lmism : ((listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
        BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
      ≠ (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin (7 * ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat + 24) base
        (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (7 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  set lol : Nat := (pfx - (0xf7 : Word)).toNat with hlol
  set dec : Word := BitVec.ofNat 64
    (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take lol)) with hdec
  set cur : Word := ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) with hcur
  have hpre := cpsTripleWithin_frameR ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) (by pcFree)
    (wi_long_to_dec base listBase listLen t0Old t1Old t2Old t3Old t4Old t5Old t6Old listBytes listOff
      hsalign hoff hover hvalid hlen h_ge h_ge_f8 hllen hlover hlvalid hoff1 h_fits h_llz_ne)
  have hLI56 := li_spec_gen_within .x6 (listBase + BitVec.ofNat 64 (listOff + 1 + lol)) (56 : Word)
    (base + 96) (by decide)
  have hLI56blk : cpsTripleWithin 1 (base + 96) (base + 100) (rlp_walk_init_code base)
      ((.x6 ↦ᵣ (listBase + BitVec.ofNat 64 (listOff + 1 + lol)))) ((.x6 ↦ᵣ (56 : Word))) := by
    runBlock hLI56
  have hbltu25 := bltu_spec_gen_within .x31 .x6 (96 : BitVec 13) dec (56 : Word) (base + 100)
  rw [show (base + 100 : Word) + 4 = base + 104 from by bv_addr] at hbltu25
  have hmono25 : ∀ a i, CodeReq.singleton (base + 100) (.BLTU .x31 .x6 (96 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 25 (base + 100)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr25 := cpsBranchWithin_ntakenPath (cpsBranchWithin_extend_code hmono25 hbltu25)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hr⟩ := hQt
      exact h_min ((sepConj_pure_right _).1 hr).2)
  have hadd26 := add_spec_gen_within .x6 .x29 .x31 cur dec (56 : Word) (base + 104) (by decide)
  have hadd26blk : cpsTripleWithin 1 (base + 104) (base + 108) (rlp_walk_init_code base)
      ((.x29 ↦ᵣ cur) ** (.x31 ↦ᵣ dec) ** (.x6 ↦ᵣ (56 : Word)))
      ((.x29 ↦ᵣ cur) ** (.x31 ↦ᵣ dec) ** (.x6 ↦ᵣ (cur + dec))) := by runBlock hadd26
  have hbne27 := bne_spec_gen_within .x6 .x11 (96 : BitVec 13) (cur + dec) (ptr + listLen) (base + 108)
  rw [show (base + 108) + signExtend13 (96 : BitVec 13) = base + 204 from by
        rw [show signExtend13 (96 : BitVec 13) = (96 : Word) from by decide]; bv_omega] at hbne27
  have hmono27 : ∀ a i, CodeReq.singleton (base + 108) (.BNE .x6 .x11 (96 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 27 (base + 108)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr27 := cpsBranchWithin_takenPath (cpsBranchWithin_extend_code hmono27 hbne27)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hr⟩ := hQf
      exact h_lmism ((sepConj_pure_right _).1 hr).2)
  have hLI := li_spec_gen_within .x12 a2Old (7 : Word) (base + 204) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 208)
  simp only [signExtend12_0] at hRet
  have hfail : cpsTripleWithin 2 (base + 204) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) ((.x12 ↦ᵣ (7 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI hRet
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hpre
    (cpsTripleWithin_frameR
      ((.x31 ↦ᵣ dec) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) **
       (.x11 ↦ᵣ (ptr + listLen)) ** regOwn .x28 ** (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
      (by pcFree) hLI56blk)
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
       regOwn .x28 ** (.x29 ↦ᵣ cur) ** (.x30 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hbr25)
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) s2 (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (ptr + listLen)) **
         regOwn .x28 ** (.x30 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hadd26blk)
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3
    (cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) ** (.x29 ↦ᵣ cur) **
       regOwn .x28 ** (.x30 ↦ᵣ (0 : Word)) ** (.x31 ↦ᵣ dec) ** (.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hbr27)
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) s4 (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (cur + dec)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xf7 : Word))) ** (.x10 ↦ᵣ ptr) **
         (.x11 ↦ᵣ (ptr + listLen)) ** (.x29 ↦ᵣ cur) ** regOwn .x28 ** (.x30 ↦ᵣ (0 : Word)) **
         (.x31 ↦ᵣ dec) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hfail)
  rw [show (7 * lol + 18 + 1 + 1 + 1 + 1 + 2) = 7 * lol + 24 from by ring] at s5
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s5
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x29)
          (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x30)
            (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x)))))))))) h hp
  xperm_hyp hp'

/-- **short list mismatch** (`0xc0 ≤ prefix < 0xf8`, `1 + (prefix-0xc0) ≠ list_len`):
    status `a2 = 3`. (wi_to_f8 ⨾ idx 6 BLTU taken ⨾ short setup ⨾ idx 35 BNE taken → idx 43,44.) -/
theorem rlp_walk_init_smism_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_smism : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
      ≠ (listBase + BitVec.ofNat 64 listOff) + listLen) :
    cpsTripleWithin 14 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (3 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  have hcls := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x1 ↦ᵣ raVal))
    (by pcFree)
    (wi_to_f8 base listBase listLen t0Old t1Old listBytes listOff hsalign hoff hover hvalid hlen h_ge)
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
  have hbne := bne_spec_gen_within .x29 .x11
    (32 : BitVec 13) (ptr + ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) (ptr + listLen)
    (base + 140)
  rw [show (base + 140) + signExtend13 (32 : BitVec 13) = base + 172 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega] at hbne
  have hmono35 : ∀ a i, CodeReq.singleton (base + 140) (.BNE .x29 .x11 (32 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 35 (base + 140)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by bv_omega))
  have hbr35 := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono35 (cpsBranchWithin_frameR
      ((.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) ** (.x7 ↦ᵣ (pfx - (0xc0 : Word))) **
        (.x28 ↦ᵣ ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x10 ↦ᵣ ptr) **
        (.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      (by pcFree) hbne))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact h_smism (by rw [hptr]; exact ((sepConj_pure_right _).1 h_pure).2))
  have hLI := li_spec_gen_within .x12 a2Old (3 : Word) (base + 172) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 176)
  simp only [signExtend12_0] at hRet
  have hfail : cpsTripleWithin 2 (base + 172) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal)) ((.x12 ↦ᵣ (3 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI hRet
  have hfail' := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ (ptr + ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)))) **
      (.x11 ↦ᵣ (ptr + listLen)) ** (.x6 ↦ᵣ (0xc0 : Word)) ** (.x5 ↦ᵣ pfx) **
      (.x7 ↦ᵣ (pfx - (0xc0 : Word))) **
      (.x28 ↦ᵣ ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))) ** (.x10 ↦ᵣ ptr) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes) (by pcFree) hfail
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcls hbr
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c1 hsetup'
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2 hbr35
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) c3 hfail'
  rw [show (6 + 1 + 4 + 1 + 2) = 14 from by norm_num] at c4
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) c4
  have hp' := sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (fun _ x => x)
      (sepConj_mono (regIs_implies_regOwn .x6) (sepConj_mono (regIs_implies_regOwn .x5)
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (fun _ x => x) (fun _ x => x)))))))) h hp
  xperm_hyp hp'

/-- **Unified strict `rlp_walk_init` dispatch.** Given the common static preconditions
    (alignment, prefix readable) and the long-list length-field validity (needed only when
    `prefix ≥ 0xf8`), the routine reaches `ra` in `≤ 81` steps, clobbers `t0..t6`, and lands
    in exactly one of the nine outcomes (status codes 0..7), distinguished by the data
    conditions in the post `⌜…⌝`. -/
theorem rlp_walk_init_spec_within
    (base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat) (hsalign : listBase.toNat % 8 = 0)
    (hoff : listOff < listBytes.length) (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hll_len : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listOff + 1 + ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat
          ≤ listBytes.length)
    (hll_over : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        listBase.toNat + (listOff + 1 +
          ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat) ≤ 2 ^ 64)
    (hll_valid : ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true →
        ∀ k, k < ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat →
          isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1 + k)) = true) :
    cpsTripleWithin 81 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x12 ↦ᵣ a2Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes) **
       (fun h =>
         -- empty (a2 = 2)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ (0 : Word)) **
            (.x12 ↦ᵣ (2 : Word)) ** ⌜listLen = (0 : Word)⌝) h) ∨
         -- not-a-list (a2 = 1)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true⌝) h) ∨
         -- short success (a2 = 0)
         (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12))) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              (listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
                = (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
         -- short mismatch (a2 = 3)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (3 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              (listBase + BitVec.ofNat 64 listOff) +
                (((listBytes[listOff]'hoff).zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
                ≠ (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
         -- long header truncated (a2 = 4)
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (4 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true⌝) h) ∨
         -- long leading zero (a2 = 5): header fits, but the first length byte is 0
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (5 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              listBytes[listOff + 1]? = some (0 : BitVec 8)⌝) h) ∨
         -- long non-minimal (a2 = 6): header fits, decoded length < 56
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (6 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true⌝) h) ∨
         -- long mismatch (a2 = 7): decoded ≥ 56 but cursor + decoded ≠ end
         (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (7 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
              ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
                  BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                    ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                ≠ (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h) ∨
         -- long success (a2 = 0): decoded ≥ 56 and cursor + decoded = end
         (((.x10 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) +
              (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))) **
            (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (0 : Word)) **
            ⌜listLen ≠ (0 : Word) ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
              ¬ BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xf8 : Word) = true ∧
              ¬ BitVec.ult ((listBase + BitVec.ofNat 64 listOff) + listLen)
                ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)))
                = true ∧
              ¬ BitVec.ult (BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))) (56 : Word) = true ∧
              ((listBase + BitVec.ofNat 64 listOff) +
                  (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))) +
                  BitVec.ofNat 64 (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take
                    ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat))
                = (listBase + BitVec.ofNat 64 listOff) + listLen⌝) h))) := by
  set ptr := listBase + BitVec.ofNat 64 listOff with hptr
  set pfx := (listBytes[listOff]'hoff).zeroExtend 64 with hpfx
  by_cases hempty : listLen = (0 : Word)
  · subst hempty
    have ht := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ ptr) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
       (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** bytesRegion listBase listBytes)
      (by pcFree) (rlp_walk_init_empty_spec_within base raVal a2Old)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
    have hp1 := sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
          (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
            (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x30)
              (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x))))))))) h hp
    refine sepConj_mono_right (fun h' hbody => Or.inl
      (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
        (sepConj_pure_right h'').2 ⟨hb, rfl⟩)) h' hbody)) h ?_
    xperm_hyp hp1
  · by_cases hnotlist : BitVec.ult pfx (0xc0 : Word) = true
    · -- not-a-list
      have ht := cpsTripleWithin_frameR
        ((.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old))
        (by pcFree)
        (rlp_walk_init_notlist_spec_within base listBase raVal listLen a2Old t0Old t1Old listBytes
          listOff hsalign hoff hover hvalid hempty hnotlist)
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
      have hp1 := sepConj_mono (fun _ x => x)
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (regIs_implies_regOwn .x29) (sepConj_mono (regIs_implies_regOwn .x30)
            (regIs_implies_regOwn .x31))))) h hp
      refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inl
        (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
          (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist⟩⟩)) h' hbody))) h ?_
      xperm_hyp hp1
    · by_cases hshort : BitVec.ult pfx (0xf8 : Word) = true
      · -- short list: success or mismatch
        by_cases hsm : ptr + ((pfx - (0xc0 : Word)) + signExtend12 (1 : BitVec 12)) = ptr + listLen
        · -- short success
          have ht := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old)) (by pcFree)
            (rlp_walk_init_short_spec_within base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old
              t4Old listBytes listOff hsalign hoff hover hvalid hempty hnotlist hshort hsm)
          refine cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
          have hp1 := sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn .x30) (regIs_implies_regOwn .x31)) h hp
          refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inl
            (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
              (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist, hshort, hsm⟩⟩)) h' hbody)))) h ?_
          xperm_hyp hp1
        · -- short mismatch
          have ht := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old)) (by pcFree)
            (rlp_walk_init_smism_spec_within base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old
              t4Old listBytes listOff hsalign hoff hover hvalid hempty hnotlist hshort hsm)
          refine cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
          have hp1 := sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn .x30) (regIs_implies_regOwn .x31)) h hp
          refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inr (Or.inl
            (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
              (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist, hshort, hsm⟩⟩)) h' hbody))))) h ?_
          xperm_hyp hp1
      · -- long list (prefix ≥ 0xf8)
        set lol : Nat := (pfx - (0xf7 : Word)).toNat with hlol
        set dec : Word := BitVec.ofNat 64
          (Nat.fromBytesBE ((listBytes.drop (listOff + 1)).take lol)) with hdec
        set cur : Word := ptr + ((pfx - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)) with hcur
        have hll_len' := hll_len hshort
        have hll_over' := hll_over hshort
        have hll_valid' := hll_valid hshort
        have hlol1 : 1 ≤ lol := by
          rw [hlol]
          simp only [BitVec.ult, decide_eq_true_eq, show (0xf8 : Word).toNat = 248 from by decide] at hshort
          have hpb : pfx.toNat < 256 := by
            rw [hpfx]; simp only [BitVec.toNat_setWidth]; have := (listBytes[listOff]'hoff).isLt; omega
          rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
        have hlol8 : lol ≤ 8 := by
          rw [hlol]
          simp only [BitVec.ult, decide_eq_true_eq, show (0xf8 : Word).toNat = 248 from by decide] at hshort
          have hpb : pfx.toNat < 256 := by
            rw [hpfx]; simp only [BitVec.toNat_setWidth]; have := (listBytes[listOff]'hoff).isLt; omega
          rw [BitVec.toNat_sub, show (0xf7 : Word).toNat = 247 from by decide]; omega
        have hde : lol = ((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)).toNat := by
          rw [hlol, hpfx]
        have hoff1 : listOff + 1 < listBytes.length := by rw [hlol] at hll_len'; omega
        have hover1 : listBase.toNat + (listOff + 1) < 2 ^ 64 := by rw [hlol] at hll_over'; omega
        have hvalid1 : isValidByteAccess (listBase + BitVec.ofNat 64 (listOff + 1)) = true := by
          have := hll_valid' 0 (by rw [hlol]; omega); simpa using this
        by_cases hfits : BitVec.ult (ptr + listLen) cur = true
        · -- ltrunc
          have ht := cpsTripleWithin_frameR ((.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old)) (by pcFree)
            (rlp_walk_init_ltrunc_spec_within base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old
              t4Old listBytes listOff hsalign hoff hover hvalid hempty hnotlist hshort hfits)
          refine cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
          have hp1 := sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn .x30) (regIs_implies_regOwn .x31)) h hp
          refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
              (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist, hshort, hfits⟩⟩)) h' hbody)))))) h ?_
          xperm_hyp hp1
        · by_cases hlz : (listBytes[listOff + 1]'hoff1).zeroExtend 64 = (0 : Word)
          · -- llz
            have ht := cpsTripleWithin_frameR ((.x31 ↦ᵣ t6Old)) (by pcFree)
              (rlp_walk_init_llz_spec_within base listBase raVal listLen a2Old t0Old t1Old t2Old t3Old
                t4Old t5Old listBytes listOff hsalign hoff hover hvalid hempty hnotlist hshort hoff1
                hover1 hvalid1 hfits hlz)
            refine cpsTripleWithin_mono_nSteps (by omega)
              (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
            have hp1 := sepConj_mono (fun _ x => x) (regIs_implies_regOwn .x31) h hp
            have hb0 : listBytes[listOff + 1]? = some (0 : BitVec 8) := by
              have hbeq : (listBytes[listOff + 1]'hoff1) = (0 : BitVec 8) := by bv_omega
              rw [List.getElem?_eq_getElem hoff1, hbeq]
            refine sepConj_mono_right (fun h' hbody => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
                (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist, hshort, hfits, hb0⟩⟩)) h' hbody)))))) ) h ?_
            xperm_hyp hp1
          · by_cases hmin : BitVec.ult dec (56 : Word) = true
            · -- lmin
              have ht := rlp_walk_init_lmin_spec_within base listBase raVal listLen a2Old t0Old t1Old
                t2Old t3Old t4Old t5Old t6Old listBytes listOff hsalign hoff hover hvalid hempty
                hnotlist hshort hll_len' hll_over' hll_valid' hoff1 hfits hlz hmin
              refine cpsTripleWithin_mono_nSteps (by omega)
                (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
              refine sepConj_mono_right (fun h' hbody =>
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
                    (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist, hshort, hfits, hmin⟩⟩))
                      h' hbody)))))))) h ?_
              xperm_hyp hp
            · by_cases hmatch : cur + dec = ptr + listLen
              · -- long success
                have ht := rlp_walk_init_long_spec_within base listBase raVal listLen a2Old t0Old t1Old
                  t2Old t3Old t4Old t5Old t6Old listBytes listOff hsalign hoff hover hvalid hempty
                  hnotlist hshort hll_len' hll_over' hll_valid' hoff1 hfits hlz hmin hmatch
                refine cpsTripleWithin_mono_nSteps (by omega)
                  (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                refine sepConj_mono_right (fun h' hbody =>
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
                      (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist, hshort, hfits, hmin, hmatch⟩⟩))
                        h' hbody))))))))) h ?_
                xperm_hyp hp
              · -- lmism
                have ht := rlp_walk_init_lmism_spec_within base listBase raVal listLen a2Old t0Old t1Old
                  t2Old t3Old t4Old t5Old t6Old listBytes listOff hsalign hoff hover hvalid hempty
                  hnotlist hshort hll_len' hll_over' hll_valid' hoff1 hfits hlz hmin hmatch
                refine cpsTripleWithin_mono_nSteps (by omega)
                  (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) ht)
                refine sepConj_mono_right (fun h' hbody =>
                  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    (sepConj_mono_right (sepConj_mono_right (fun h'' hb =>
                      (sepConj_pure_right h'').2 ⟨hb, ⟨hempty, hnotlist, hshort, hfits, hmin, hmatch⟩⟩))
                        h' hbody)))))))) ) h ?_
                xperm_hyp hp

end EvmAsm.Rv64.RLP
