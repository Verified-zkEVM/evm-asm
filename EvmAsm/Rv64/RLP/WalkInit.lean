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

  Lays out the 17-instruction body `rlp_walk_init_prog`. Proved: the
  **not-a-list** path (status 1). Follow-ups (stacked-PR sequence): the
  short-list and long-list paths (status 0) and the unified disjunctive theorem.
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
  [ .ADD .x11 .x10 .x11,            -- 0
    .LBU .x5 .x10 0,                -- 1
    .LI .x6 (0xc0 : Word),          -- 2
    .BLTU .x5 .x6 (48 : BitVec 13), -- 3
    .LI .x6 (0xf8 : Word),          -- 4
    .BLTU .x5 .x6 (28 : BitVec 13), -- 5
    .LI .x6 (0xf7 : Word),          -- 6
    .SUB .x7 .x5 .x6,               -- 7
    .ADDI .x7 .x7 (1 : BitVec 12),  -- 8
    .ADD .x10 .x10 .x7,             -- 9
    .LI .x12 (0 : Word),            -- 10
    .JALR .x0 .x1 0,                -- 11
    .ADDI .x10 .x10 (1 : BitVec 12),-- 12
    .LI .x12 (0 : Word),            -- 13
    .JALR .x0 .x1 0,                -- 14
    .LI .x12 (1 : Word),            -- 15
    .JALR .x0 .x1 0 ]               -- 16

theorem rlp_walk_init_prog_length : rlp_walk_init_prog.length = 17 := rfl

abbrev rlp_walk_init_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_walk_init_prog

instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/--
**`rlp_walk_init` — not-a-list path.**

When the prefix byte is `< 0xc0` (not an RLP list), the routine returns status
`a2 = 1`, leaves the cursor `a0` at the list pointer, and reports
`a1 = list_ptr + list_len`. Scratch `t0`/`t1` clobbered; `ra` preserved.
-/
theorem rlp_walk_init_fail_spec_within
    (base listBase raVal listLen a2Old t1Old : Word) (listBytes : List (BitVec 8)) (listOff : Nat)
    (hsalign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (hfail : BitVec.ult ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) = true) :
    cpsTripleWithin 6 base (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
        (.x12 ↦ᵣ a2Old) ** (.x5 ↦ᵣ t1Old) ** (.x6 ↦ᵣ t1Old) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion listBase listBytes) := by
  -- Phase A: ADD x11 x10 x11 ; LBU x5 x10 0 ; LI x6 0xc0 (idx 0,1,2).  base → base+12.
  have hadd := add_spec_gen_rd_eq_rs2_within .x11 .x10 (listBase + BitVec.ofNat 64 listOff) listLen
    (base) (by decide)
  have hlbu := bytesRegion_lbu_within .x5 .x10 listBase t1Old (base + 4) listBytes listOff
    (by decide) hsalign hoff hover hvalid
  have hLI := li_spec_gen_within .x6 t1Old (0xc0 : Word) (base + 8) (by decide)
  have hA : cpsTripleWithin 3 base (base + 12) (rlp_walk_init_code base)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) ** (.x5 ↦ᵣ t1Old) **
        (.x6 ↦ᵣ t1Old) ** bytesRegion listBase listBytes)
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
        (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xc0 : Word)) **
        bytesRegion listBase listBytes) := by
    runBlock hadd hlbu hLI
  have hA' := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ a2Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal)) (by pcFree) hA
  -- Phase B: BLTU x5 x6 48 TAKEN (prefix < 0xc0), idx 3.  base+12 → base+60 (fail).
  have hbltu := bltu_spec_gen_within .x5 .x6 (48 : BitVec 13)
    ((listBytes[listOff]'hoff).zeroExtend 64) (0xc0 : Word) (base + 12)
  rw [show (base + 12) + signExtend13 (48 : BitVec 13) = base + 60 from by
        rw [show signExtend13 (48 : BitVec 13) = (48 : Word) from by decide]; bv_omega,
      show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbltu
  have hmono3 : ∀ a i, CodeReq.singleton (base + 12) (.BLTU .x5 .x6 (48 : BitVec 13)) a = some i
      → rlp_walk_init_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_walk_init_prog 3 (base + 12)
      (by rw [rlp_walk_init_prog_length]; norm_num)
      (by rw [rlp_walk_init_prog_length]; norm_num) (by rfl))
  have hB := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono3 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
        (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) ** (.x12 ↦ᵣ a2Old) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion listBase listBytes)
      (by pcFree) hbltu))
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 hfail)
  -- Phase C: LI x12 1 ; ret (idx 15, 16).  base+60 → ra &&& ~~~1.
  have hLI1 := li_spec_gen_within .x12 a2Old (1 : Word) (base + 60) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (base + 64)
  simp only [signExtend12_0] at hRet
  have hC : cpsTripleWithin 2 (base + 60) (raVal &&& ~~~1) (rlp_walk_init_code base)
      ((.x12 ↦ᵣ a2Old) ** (.x1 ↦ᵣ raVal))
      ((.x12 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ raVal)) := by
    runBlock hLI1 hRet
  have hC' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) **
      (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
      (.x5 ↦ᵣ (listBytes[listOff]'hoff).zeroExtend 64) ** (.x6 ↦ᵣ (0xc0 : Word)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase listBytes)
    (by pcFree) hC
  -- Compose A ⨾ B(taken) ⨾ C.
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA' hB
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2) s1 hC'
  rw [show (3 + 1 + 2) = 6 from rfl] at s2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s2
  have hp' := sepConj_mono_right (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
      (fun _ x => x))))) h hp
  xperm_hyp hp'

-- Sanity: program length + key instruction lookups.
example : rlp_walk_init_prog.length = 17 := rfl
example : (CodeReq.ofProg (0 : Word) rlp_walk_init_prog) 12 =
    some (.BLTU .x5 .x6 (48 : BitVec 13)) := by decide

end EvmAsm.Rv64.RLP
