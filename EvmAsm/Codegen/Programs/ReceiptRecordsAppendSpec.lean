/-
  EvmAsm.Codegen.Programs.ReceiptRecordsAppendSpec

  Flat-layer whole-routine triples for `receipt_records_append` — the
  receipt-record bundle entry the DCode layer cannot port (it reads the
  control block AND writes the separately-pointed record arena: two
  writable regions against DCode's single `RwRegion`; see #12991).  The
  flat layer carries both regions natively as `**`-separated dword cells.

  Both arms are covered: `receiptRecordsAppend_spec_within_ok` (capacity
  available: the record slot receives the seven arguments plus the
  reserved zero, the count increments, `a0 = 0`) and
  `receiptRecordsAppend_spec_within_full` (capacity reached: nothing is
  written, `a0 = 1`).

  Instruction indices (into `receiptRecordsAppendProg`, entry `base`):
    0-1   ld t0/t1 (count, capacity)
    2     bgeu t0, t1, +64 (→ index 18, the full tail)
    3-5   ld t2 (record base); slli t3, t0, 6; add t2, t2, t3
    6-13  eight sd into the 64-byte record slot
    14-16 addi t0, t0, 1; sd t0, 0(a0); li a0, 0
    17    ret
    18-19 li a0, 1; ret
-/

import EvmAsm.Codegen.Programs.ReceiptRecordsProgs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen

namespace ReceiptRecordsAppendSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The routine's own image at `base`. -/
abbrev rraCode (base : Word) : CodeReq :=
  CodeReq.ofProg base receiptRecordsAppendProg

private theorem rraProg_len : (receiptRecordsAppendProg : List Instr).length = 20 := by
  decide

private theorem rraProg_bound :
    4 * (receiptRecordsAppendProg : List Instr).length < 2 ^ 64 := by
  rw [rraProg_len]; norm_num

private theorem rra_mem (base : Word) (k : Nat) (ins : Instr) (A : Word)
    (hA : A = base + BitVec.ofNat 64 (4 * k))
    (hk : k < (receiptRecordsAppendProg : List Instr).length)
    (hins : (receiptRecordsAppendProg : List Instr)[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → rraCode base a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at base A receiptRecordsAppendProg k ins hA hk hins
      rraProg_bound a i h

set_option maxRecDepth 8000 in
/-- **`receipt_records_append`, success arm** (`cnt <ᵤ cap`): the eight
    dwords of the record at `rbase + (cnt <<< 6)` become
    `v1..v7, 0`, the count cell becomes `cnt + 1`, and `a0 = 0`. -/
theorem receiptRecordsAppend_spec_within_ok
    (base ret ctl cnt cap rbase : Word)
    (v1 v2 v3 v4 v5 v6 v7 : Word)
    (t0Old t1Old t2Old t3Old : Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Word)
    (hlt : BitVec.ult cnt cap) :
    cpsTripleWithin 18 base (ret &&& ~~~1) (rraCode base)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
        (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ m0) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) **
        (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) **
        (.x17 ↦ᵣ v7) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (cnt + 1)) ** (.x6 ↦ᵣ cap) **
        (.x7 ↦ᵣ (rbase + (cnt <<< 6))) ** (.x28 ↦ᵣ (cnt <<< 6)) **
        (ctl ↦ₘ (cnt + 1)) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ v1) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ v2) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ v3) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ v4) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ v5) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ v6) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ v7) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ (0 : Word))) := by
  set slot := rbase + (cnt <<< 6) with hslot
  -- ---- idx 0-1: load count and capacity ----
  have hld0 := ld_spec_gen_within .x5 .x10 ctl t0Old cnt (0 : BitVec 12)
    base (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ctl + (0 : Word) = ctl from by bv_omega] at hld0
  have hld1 := ld_spec_gen_within .x6 .x10 ctl t1Old cap (8 : BitVec 12)
    (base + 4) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hld1
  have hLoads : cpsTripleWithin 2 base (base + 8) (rraCode base)
      ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap))
      ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ cap) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap)) := by
    runBlock hld0 hld1
  -- ---- idx 2: bgeu not taken (cnt <u cap) ----
  have hbgeu := bgeu_spec_gen_within .x5 .x6 (64 : BitVec 13) cnt cap (base + 8)
  rw [show (base + 8 : Word) + 4 = base + 12 from by
        rw [BitVec.add_assoc]; rfl] at hbgeu
  have hmono2 : ∀ a' i, CodeReq.singleton (base + 8)
      (.BGEU .x5 .x6 (64 : BitVec 13)) a' = some i → rraCode base a' = some i :=
    rra_mem base 2 _ (base + 8) (by rw [show (4 * 2 : Nat) = 8 from rfl]; rfl)
      (by rw [rraProg_len]; omega) (by rfl)
  have hBr := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono2 hbgeu)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd hlt (((sepConj_pure_right _).1 h_pure).2))
  -- ---- idx 3-5: record base, slot offset, slot pointer ----
  have hld2 := ld_spec_gen_within .x7 .x10 ctl t2Old rbase (16 : BitVec 12)
    (base + 12) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hld2
  have hslli := slli_spec_gen_within .x28 .x5 t3Old cnt (6 : BitVec 6)
    (base + 16) (by decide)
  rw [show BitVec.toNat (6 : BitVec 6) = 6 from by decide] at hslli
  have hadd := add_spec_gen_rd_eq_rs1_within .x7 .x28 rbase (cnt <<< 6)
    (base + 20) (by decide)
  rw [← hslot] at hadd
  have hAddr : cpsTripleWithin 3 (base + 12) (base + 24) (rraCode base)
      ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ cnt) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        ((ctl + 16) ↦ₘ rbase))
      ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ cnt) ** (.x7 ↦ᵣ slot) **
        (.x28 ↦ᵣ (cnt <<< 6)) ** ((ctl + 16) ↦ₘ rbase)) := by
    runBlock hld2 hslli hadd
  -- ---- idx 6-13: the eight record stores ----
  have hsd0 := sd_spec_gen_within .x7 .x11 slot v1 m0 (0 : BitVec 12) (base + 24)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show slot + (0 : Word) = slot from by bv_omega] at hsd0
  have hsd1 := sd_spec_gen_within .x7 .x12 slot v2 m1 (8 : BitVec 12) (base + 28)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hsd1
  have hsd2 := sd_spec_gen_within .x7 .x13 slot v3 m2 (16 : BitVec 12) (base + 32)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hsd2
  have hsd3 := sd_spec_gen_within .x7 .x14 slot v4 m3 (24 : BitVec 12) (base + 36)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at hsd3
  have hsd4 := sd_spec_gen_within .x7 .x15 slot v5 m4 (32 : BitVec 12) (base + 40)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at hsd4
  have hsd5 := sd_spec_gen_within .x7 .x16 slot v6 m5 (40 : BitVec 12) (base + 44)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at hsd5
  have hsd6 := sd_spec_gen_within .x7 .x17 slot v7 m6 (48 : BitVec 12) (base + 48)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at hsd6
  have hsd7 := sd_x0_spec_gen_within .x7 slot m7 (56 : BitVec 12) (base + 52)
  rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide] at hsd7
  have hStores : cpsTripleWithin 8 (base + 24) (base + 56) (rraCode base)
      ((.x7 ↦ᵣ slot) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
        (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
        (slot ↦ₘ m0) ** ((slot + 8) ↦ₘ m1) ** ((slot + 16) ↦ₘ m2) **
        ((slot + 24) ↦ₘ m3) ** ((slot + 32) ↦ₘ m4) ** ((slot + 40) ↦ₘ m5) **
        ((slot + 48) ↦ₘ m6) ** ((slot + 56) ↦ₘ m7))
      ((.x7 ↦ᵣ slot) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
        (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
        (slot ↦ₘ v1) ** ((slot + 8) ↦ₘ v2) ** ((slot + 16) ↦ₘ v3) **
        ((slot + 24) ↦ₘ v4) ** ((slot + 32) ↦ₘ v5) ** ((slot + 40) ↦ₘ v6) **
        ((slot + 48) ↦ₘ v7) ** ((slot + 56) ↦ₘ (0 : Word))) := by
    runBlock hsd0 hsd1 hsd2 hsd3 hsd4 hsd5 hsd6 hsd7
  -- ---- idx 14-16: count increment, writeback, success flag ----
  have haddi := addi_spec_gen_same_within .x5 cnt (1 : BitVec 12)
    (base + 56) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at haddi
  have hsdc := sd_spec_gen_within .x10 .x5 ctl (cnt + 1) cnt (0 : BitVec 12)
    (base + 60)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ctl + (0 : Word) = ctl from by bv_omega] at hsdc
  have hli := li_spec_gen_within .x10 ctl (0 : Word) (base + 64) (by decide)
  have hFinish : cpsTripleWithin 3 (base + 56) (base + 68) (rraCode base)
      ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ cnt) ** (ctl ↦ₘ cnt))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (cnt + 1)) ** (ctl ↦ₘ (cnt + 1))) := by
    runBlock haddi hsdc hli
  -- ---- idx 17: ret ----
  have hret := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (base + 68)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (ret + 0 : Word) = ret from by bv_omega] at hret
  have hmono17 : ∀ a' i, CodeReq.singleton (base + 68)
      (.JALR .x0 .x1 (0 : BitVec 12)) a' = some i → rraCode base a' = some i :=
    rra_mem base 17 _ (base + 68) (by rw [show (4 * 17 : Nat) = 68 from rfl]; rfl)
      (by rw [rraProg_len]; omega) (by rfl)
  have hRet := cpsTripleWithin_extend_code hmono17 hret
  -- ---- frame and compose ----
  have hLoadsF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) **
      (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      ((ctl + 16) ↦ₘ rbase) **
      (slot ↦ₘ m0) ** ((slot + 8) ↦ₘ m1) ** ((slot + 16) ↦ₘ m2) **
      ((slot + 24) ↦ₘ m3) ** ((slot + 32) ↦ₘ m4) ** ((slot + 40) ↦ₘ m5) **
      ((slot + 48) ↦ₘ m6) ** ((slot + 56) ↦ₘ m7))
    (by pcFree) hLoads
  have hBrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
      (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      (slot ↦ₘ m0) ** ((slot + 8) ↦ₘ m1) ** ((slot + 16) ↦ₘ m2) **
      ((slot + 24) ↦ₘ m3) ** ((slot + 32) ↦ₘ m4) ** ((slot + 40) ↦ₘ m5) **
      ((slot + 48) ↦ₘ m6) ** ((slot + 56) ↦ₘ m7))
    (by pcFree) hBr
  have hAddrF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) **
      (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ cap) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) **
      (slot ↦ₘ m0) ** ((slot + 8) ↦ₘ m1) ** ((slot + 16) ↦ₘ m2) **
      ((slot + 24) ↦ₘ m3) ** ((slot + 32) ↦ₘ m4) ** ((slot + 40) ↦ₘ m5) **
      ((slot + 48) ↦ₘ m6) ** ((slot + 56) ↦ₘ m7))
    (by pcFree) hAddr
  have hStoresF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ cap) ** (.x28 ↦ᵣ (cnt <<< 6)) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase))
    (by pcFree) hStores
  have hFinishF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) **
      (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ cap) **
      (.x7 ↦ᵣ slot) ** (.x28 ↦ᵣ (cnt <<< 6)) **
      ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      (slot ↦ₘ v1) ** ((slot + 8) ↦ₘ v2) ** ((slot + 16) ↦ₘ v3) **
      ((slot + 24) ↦ₘ v4) ** ((slot + 32) ↦ₘ v5) ** ((slot + 40) ↦ₘ v6) **
      ((slot + 48) ↦ₘ v7) ** ((slot + 56) ↦ₘ (0 : Word)))
    (by pcFree) hFinish
  have hRetF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
      (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
      (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ (cnt + 1)) ** (.x6 ↦ᵣ cap) ** (.x7 ↦ᵣ slot) **
      (.x28 ↦ᵣ (cnt <<< 6)) **
      (ctl ↦ₘ (cnt + 1)) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      (slot ↦ₘ v1) ** ((slot + 8) ↦ₘ v2) ** ((slot + 16) ↦ₘ v3) **
      ((slot + 24) ↦ₘ v4) ** ((slot + 32) ↦ₘ v5) ** ((slot + 40) ↦ₘ v6) **
      ((slot + 48) ↦ₘ v7) ** ((slot + 56) ↦ₘ (0 : Word)))
    (by pcFree) hRet
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hLoadsF hBrF
    intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hAddrF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hStoresF
    intro h hp; xperm_hyp hp
  have s4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s3 hFinishF
    intro h hp; xperm_hyp hp
  have s5 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s4 hRetF
    intro h hp; xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s5

set_option maxRecDepth 8000 in
/-- **`receipt_records_append`, capacity-full arm** (`¬ cnt <ᵤ cap`):
    nothing is written and `a0 = 1`. -/
theorem receiptRecordsAppend_spec_within_full
    (base ret ctl cnt cap : Word)
    (t0Old t1Old : Word)
    (hge : ¬ BitVec.ult cnt cap) :
    cpsTripleWithin 5 base (ret &&& ~~~1) (rraCode base)
      ((.x10 ↦ᵣ ctl) ** (.x1 ↦ᵣ ret) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x1 ↦ᵣ ret) **
        (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ cap) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap)) := by
  -- ---- idx 0-1: load count and capacity ----
  have hld0 := ld_spec_gen_within .x5 .x10 ctl t0Old cnt (0 : BitVec 12)
    base (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ctl + (0 : Word) = ctl from by bv_omega] at hld0
  have hld1 := ld_spec_gen_within .x6 .x10 ctl t1Old cap (8 : BitVec 12)
    (base + 4) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hld1
  have hLoads : cpsTripleWithin 2 base (base + 8) (rraCode base)
      ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap))
      ((.x10 ↦ᵣ ctl) ** (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ cap) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap)) := by
    runBlock hld0 hld1
  -- ---- idx 2: bgeu taken (cnt ≥u cap), to base + 72 ----
  have hbgeu := bgeu_spec_gen_within .x5 .x6 (64 : BitVec 13) cnt cap (base + 8)
  rw [show (base + 8 : Word) + signExtend13 (64 : BitVec 13) = base + 72 from by
        rw [show signExtend13 (64 : BitVec 13) = (64 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hbgeu
  have hmono2 : ∀ a' i, CodeReq.singleton (base + 8)
      (.BGEU .x5 .x6 (64 : BitVec 13)) a' = some i → rraCode base a' = some i :=
    rra_mem base 2 _ (base + 8) (by rw [show (4 * 2 : Nat) = 8 from rfl]; rfl)
      (by rw [rraProg_len]; omega) (by rfl)
  have hBr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono2 hbgeu)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hge)
  -- ---- idx 18: li a0, 1 ----
  have hli := li_spec_gen_within .x10 ctl (1 : Word) (base + 72) (by decide)
  have hmono18 : ∀ a' i, CodeReq.singleton (base + 72)
      (.LI .x10 (1 : Word)) a' = some i → rraCode base a' = some i :=
    rra_mem base 18 _ (base + 72) (by rw [show (4 * 18 : Nat) = 72 from rfl]; rfl)
      (by rw [rraProg_len]; omega) (by rfl)
  have hLi := cpsTripleWithin_extend_code hmono18 hli
  rw [show (base + 72 : Word) + 4 = base + 76 from by
        rw [BitVec.add_assoc]; rfl] at hLi
  -- ---- idx 19: ret ----
  have hret := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (base + 76)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (ret + 0 : Word) = ret from by bv_omega] at hret
  have hmono19 : ∀ a' i, CodeReq.singleton (base + 76)
      (.JALR .x0 .x1 (0 : BitVec 12)) a' = some i → rraCode base a' = some i :=
    rra_mem base 19 _ (base + 76) (by rw [show (4 * 19 : Nat) = 76 from rfl]; rfl)
      (by rw [rraProg_len]; omega) (by rfl)
  have hRet := cpsTripleWithin_extend_code hmono19 hret
  -- ---- frame and compose ----
  have hBrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x1 ↦ᵣ ret) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap))
    (by pcFree) hBr
  have hLiF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ cap) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap))
    (by pcFree) hLi
  have hRetF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ cap) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap))
    (by pcFree) hRet
  have hLoadsF := cpsTripleWithin_frameR ((.x1 : Reg) ↦ᵣ ret)
    (by pcFree) hLoads
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hLoadsF hBrF
    intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hLiF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hRetF
    intro h hp; xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s3

/-! ## The bundle image, and the cross-entry composition (#12991)

    `receipt_records_append_runtime_result` ends with `jal x0, .-108`
    INTO `receipt_records_append` — the edge that makes the receipt unit
    a genuine bundle.  Both the append triple and the runtime-result
    triple below are stated over the ONE shared
    `CodeReq.ofProg bundleBase receiptRecordsBundleProg`, so the jump
    target's code identity is already in hand and the composition is a
    plain `seq`. -/

/-- The full five-entry bundle image at `bundleBase`. -/
abbrev rrBundleCode (bundleBase : Word) : CodeReq :=
  CodeReq.ofProg bundleBase receiptRecordsBundleProg

private theorem rrbProg_len :
    (receiptRecordsBundleProg : List Instr).length = 61 := by decide

private theorem rrbProg_bound :
    4 * (receiptRecordsBundleProg : List Instr).length < 2 ^ 64 := by
  rw [rrbProg_len]; norm_num

private theorem rrb_mem (bundleBase : Word) (k : Nat) (ins : Instr) (A : Word)
    (hA : A = bundleBase + BitVec.ofNat 64 (4 * k))
    (hk : k < (receiptRecordsBundleProg : List Instr).length)
    (hins : (receiptRecordsBundleProg : List Instr)[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      rrBundleCode bundleBase a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at bundleBase A receiptRecordsBundleProg k ins hA hk
      hins rrbProg_bound a i h

/-- The append success arm over the SHARED bundle image (entry
    `bundleBase + 32`, bundle instruction index 8). -/
theorem receiptRecordsAppend_bundleSpec_ok
    (bundleBase ret ctl cnt cap rbase : Word)
    (v1 v2 v3 v4 v5 v6 v7 : Word)
    (t0Old t1Old t2Old t3Old : Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Word)
    (hlt : BitVec.ult cnt cap) :
    cpsTripleWithin 18 (bundleBase + 32) (ret &&& ~~~1)
      (rrBundleCode bundleBase)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
        (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) ** (.x17 ↦ᵣ v7) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ m0) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) **
        (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ v6) **
        (.x17 ↦ᵣ v7) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (cnt + 1)) ** (.x6 ↦ᵣ cap) **
        (.x7 ↦ᵣ (rbase + (cnt <<< 6))) ** (.x28 ↦ᵣ (cnt <<< 6)) **
        (ctl ↦ₘ (cnt + 1)) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ v1) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ v2) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ v3) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ v4) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ v5) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ v6) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ v7) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ (0 : Word))) :=
  cpsTripleWithin_extend_code
    (fun a i h =>
      CodeReq.ofProg_mono_sub bundleBase (bundleBase + 32)
        (receiptRecordsBundleProg : List Instr)
        (receiptRecordsAppendProg : List Instr) 8
        rfl (by decide) (by decide) (by decide) a i h)
    (receiptRecordsAppend_spec_within_ok (bundleBase + 32) ret ctl cnt cap
      rbase v1 v2 v3 v4 v5 v6 v7 t0Old t1Old t2Old t3Old
      m0 m1 m2 m3 m4 m5 m6 m7 hlt)

set_option maxRecDepth 8000 in
/-- **The cross-entry composition** (#12991's flagship):
    `receipt_records_append_runtime_result` on the committed-logs path
    (`a2 ≠ 0`, checkpoint `a4 ≤ᵤ` final `a5`, capacity available) —
    normalize `a5 := a5 - a4`, zero `a6`/`a7`, tail-jump into
    `receipt_records_append` (entry `bundleBase + 32`), and return from
    THERE with the record appended.  One triple over the ONE bundle
    image; the other input cases are mechanical clones. -/
theorem receiptRecordsAppendRuntime_spec_within_committed
    (bundleBase ret ctl cnt cap rbase : Word)
    (v1 v2 v3 v4 v5 g6 g7 : Word)
    (t0Old t1Old t2Old t3Old : Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Word)
    (hlt : BitVec.ult cnt cap)
    (hstatus : v2 ≠ 0)
    (hlogs : ¬ BitVec.ult v5 v4) :
    cpsTripleWithin 25 (bundleBase + 112) (ret &&& ~~~1)
      (rrBundleCode bundleBase)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
        (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ m0) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) **
        (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ (v5 - v4)) **
        (.x16 ↦ᵣ (0 : Word)) ** (.x17 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (cnt + 1)) ** (.x6 ↦ᵣ cap) **
        (.x7 ↦ᵣ (rbase + (cnt <<< 6))) ** (.x28 ↦ᵣ (cnt <<< 6)) **
        (ctl ↦ₘ (cnt + 1)) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ v1) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ v2) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ v3) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ v4) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ (v5 - v4)) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ (0 : Word))) := by
  set E := bundleBase + 112 with hE
  -- ---- bundle idx 28: beq x12 x0 +16, not taken (v2 ≠ 0) ----
  have hbeq := beq_spec_gen_within .x12 .x0 (16 : BitVec 13) v2 (0 : Word) E
  rw [show (E + 4 : Word) = bundleBase + 116 from by
        rw [hE, BitVec.add_assoc]; rfl] at hbeq
  have hmono28 : ∀ a' i, CodeReq.singleton E
      (.BEQ .x12 .x0 (16 : BitVec 13)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 28 _ E (by rw [hE]; rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hBeq := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono28 hbeq)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hstatus)
  -- ---- bundle idx 29: bltu x15 x14 +12, not taken (¬ v5 <u v4) ----
  have hbltu := bltu_spec_gen_within .x15 .x14 (12 : BitVec 13) v5 v4
    (bundleBase + 116)
  rw [show (bundleBase + 116 : Word) + 4 = bundleBase + 120 from by
        rw [BitVec.add_assoc]; rfl] at hbltu
  have hmono29 : ∀ a' i, CodeReq.singleton (bundleBase + 116)
      (.BLTU .x15 .x14 (12 : BitVec 13)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 29 _ (bundleBase + 116) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hBltu := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono29 hbltu)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hlogs)
  -- ---- bundle idx 30: sub x15 x15 x14 ----
  have hsub := sub_spec_gen_rd_eq_rs1_within .x15 .x14 v5 v4
    (bundleBase + 120) (by decide)
  have hmono30 : ∀ a' i, CodeReq.singleton (bundleBase + 120)
      (.SUB .x15 .x15 .x14) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 30 _ (bundleBase + 120) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hSub := cpsTripleWithin_extend_code hmono30 hsub
  rw [show (bundleBase + 120 : Word) + 4 = bundleBase + 124 from by
        rw [BitVec.add_assoc]; rfl] at hSub
  -- ---- bundle idx 31: jal x0 +8 (skip the zero arm) ----
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (bundleBase + 124)
  rw [show (bundleBase + 124 : Word) + signExtend21 (8 : BitVec 21)
        = bundleBase + 132 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hjal
  have hmono31 : ∀ a' i, CodeReq.singleton (bundleBase + 124)
      (.JAL .x0 (8 : BitVec 21)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 31 _ (bundleBase + 124) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hJal := cpsTripleWithin_extend_code hmono31 hjal
  -- ---- bundle idx 33-34: li x16, 0 ; li x17, 0 ----
  have hli6 := li_spec_gen_within .x16 g6 (0 : Word) (bundleBase + 132)
    (by decide)
  have hmono33 : ∀ a' i, CodeReq.singleton (bundleBase + 132)
      (.LI .x16 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 33 _ (bundleBase + 132) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi6 := cpsTripleWithin_extend_code hmono33 hli6
  rw [show (bundleBase + 132 : Word) + 4 = bundleBase + 136 from by
        rw [BitVec.add_assoc]; rfl] at hLi6
  have hli7 := li_spec_gen_within .x17 g7 (0 : Word) (bundleBase + 136)
    (by decide)
  have hmono34 : ∀ a' i, CodeReq.singleton (bundleBase + 136)
      (.LI .x17 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 34 _ (bundleBase + 136) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi7 := cpsTripleWithin_extend_code hmono34 hli7
  rw [show (bundleBase + 136 : Word) + 4 = bundleBase + 140 from by
        rw [BitVec.add_assoc]; rfl] at hLi7
  -- ---- bundle idx 35: jal x0 -108, INTO receipt_records_append ----
  have hjmp := jal_x0_spec_gen_within (-108 : BitVec 21) (bundleBase + 140)
  rw [show (bundleBase + 140 : Word) + signExtend21 (-108 : BitVec 21)
        = bundleBase + 32 from by
        rw [show signExtend21 (-108 : BitVec 21)
              = (0xFFFFFFFFFFFFFF94 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hjmp
  have hmono35 : ∀ a' i, CodeReq.singleton (bundleBase + 140)
      (.JAL .x0 (-108 : BitVec 21)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 35 _ (bundleBase + 140) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hJmp := cpsTripleWithin_extend_code hmono35 hjmp
  -- ---- the append callee, over the same bundle image ----
  have hAppend := receiptRecordsAppend_bundleSpec_ok bundleBase ret ctl cnt
    cap rbase v1 v2 v3 v4 (v5 - v4) (0 : Word) (0 : Word)
    t0Old t1Old t2Old t3Old m0 m1 m2 m3 m4 m5 m6 m7 hlt
  -- ---- fuse the straight-line middle (sub ; jal ; li ; li ; jmp) ----
  have hMid : cpsTripleWithin 5 (bundleBase + 120) (bundleBase + 32)
      (rrBundleCode bundleBase)
      ((.x15 ↦ᵣ v5) ** (.x14 ↦ᵣ v4) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7))
      ((.x15 ↦ᵣ (v5 - v4)) ** (.x14 ↦ᵣ v4) ** (.x16 ↦ᵣ (0 : Word)) **
        (.x17 ↦ᵣ (0 : Word))) := by
    runBlock hSub hJal hLi6 hLi7 hJmp
  -- ---- frame each piece to the full state ----
  have hBeqF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x13 ↦ᵣ v3) **
      (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
      (.x1 ↦ᵣ ret) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hBeq
  have hBltuF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
      (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hBltu
  have hMidF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hMid
  -- ---- compose: beq ⨾ bltu ⨾ mid ⨾ append ----
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hBeqF hBltuF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hMidF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hAppend
    intro h hp; xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s3

set_option maxRecDepth 8000 in
/-- The no-logs input case (`a2 = 0`, a reverted/failing tx): the `beq`
    takes straight to the zeroing arm, so the record is appended with
    `log count = 0` (and zero encoder fields). -/
theorem receiptRecordsAppendRuntime_spec_within_noLogs
    (bundleBase ret ctl cnt cap rbase : Word)
    (v1 v3 v4 v5 g6 g7 : Word)
    (t0Old t1Old t2Old t3Old : Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Word)
    (hlt : BitVec.ult cnt cap) :
    cpsTripleWithin 23 (bundleBase + 112) (ret &&& ~~~1)
      (rrBundleCode bundleBase)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ v3) **
        (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ m0) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ (0 : Word)) ** (.x17 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (cnt + 1)) ** (.x6 ↦ᵣ cap) **
        (.x7 ↦ᵣ (rbase + (cnt <<< 6))) ** (.x28 ↦ᵣ (cnt <<< 6)) **
        (ctl ↦ₘ (cnt + 1)) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ v1) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ v3) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ v4) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ (0 : Word))) := by
  set E := bundleBase + 112 with hE
  -- ---- bundle idx 28: beq x12 x0 +16, TAKEN (a2 = 0) → idx 32 ----
  have hbeq := beq_spec_gen_within .x12 .x0 (16 : BitVec 13) (0 : Word)
    (0 : Word) E
  rw [show (E : Word) + signExtend13 (16 : BitVec 13) = bundleBase + 128
        from by
        rw [hE, show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hbeq
  have hmono28 : ∀ a' i, CodeReq.singleton E
      (.BEQ .x12 .x0 (16 : BitVec 13)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 28 _ E (by rw [hE]; rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hBeq := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono28 hbeq)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  -- ---- bundle idx 32-34: li x15/x16/x17, 0 ; idx 35: jal into append ----
  have hli5 := li_spec_gen_within .x15 v5 (0 : Word) (bundleBase + 128)
    (by decide)
  have hmono32 : ∀ a' i, CodeReq.singleton (bundleBase + 128)
      (.LI .x15 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 32 _ (bundleBase + 128) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi5 := cpsTripleWithin_extend_code hmono32 hli5
  rw [show (bundleBase + 128 : Word) + 4 = bundleBase + 132 from by
        rw [BitVec.add_assoc]; rfl] at hLi5
  have hli6 := li_spec_gen_within .x16 g6 (0 : Word) (bundleBase + 132)
    (by decide)
  have hmono33 : ∀ a' i, CodeReq.singleton (bundleBase + 132)
      (.LI .x16 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 33 _ (bundleBase + 132) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi6 := cpsTripleWithin_extend_code hmono33 hli6
  rw [show (bundleBase + 132 : Word) + 4 = bundleBase + 136 from by
        rw [BitVec.add_assoc]; rfl] at hLi6
  have hli7 := li_spec_gen_within .x17 g7 (0 : Word) (bundleBase + 136)
    (by decide)
  have hmono34 : ∀ a' i, CodeReq.singleton (bundleBase + 136)
      (.LI .x17 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 34 _ (bundleBase + 136) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi7 := cpsTripleWithin_extend_code hmono34 hli7
  rw [show (bundleBase + 136 : Word) + 4 = bundleBase + 140 from by
        rw [BitVec.add_assoc]; rfl] at hLi7
  have hjmp := jal_x0_spec_gen_within (-108 : BitVec 21) (bundleBase + 140)
  rw [show (bundleBase + 140 : Word) + signExtend21 (-108 : BitVec 21)
        = bundleBase + 32 from by
        rw [show signExtend21 (-108 : BitVec 21)
              = (0xFFFFFFFFFFFFFF94 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hjmp
  have hmono35 : ∀ a' i, CodeReq.singleton (bundleBase + 140)
      (.JAL .x0 (-108 : BitVec 21)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 35 _ (bundleBase + 140) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hJmp := cpsTripleWithin_extend_code hmono35 hjmp
  have hMid : cpsTripleWithin 4 (bundleBase + 128) (bundleBase + 32)
      (rrBundleCode bundleBase)
      ((.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7))
      ((.x15 ↦ᵣ (0 : Word)) ** (.x16 ↦ᵣ (0 : Word)) **
        (.x17 ↦ᵣ (0 : Word))) := by
    runBlock hLi5 hLi6 hLi7 hJmp
  -- ---- the append callee ----
  have hAppend := receiptRecordsAppend_bundleSpec_ok bundleBase ret ctl cnt
    cap rbase v1 (0 : Word) v3 v4 (0 : Word) (0 : Word) (0 : Word)
    t0Old t1Old t2Old t3Old m0 m1 m2 m3 m4 m5 m6 m7 hlt
  -- ---- frame and compose ----
  have hBeqF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x13 ↦ᵣ v3) **
      (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
      (.x1 ↦ᵣ ret) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hBeq
  have hMidF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ (0 : Word)) **
      (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hMid
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hBeqF hMidF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hAppend
    intro h hp; xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s2

set_option maxRecDepth 8000 in
/-- The reverted-window input case (`a2 ≠ 0` but the final log cursor
    `a5` is below the checkpoint `a4`): the `bltu` takes to the zeroing
    arm, so the record is appended with `log count = 0`. -/
theorem receiptRecordsAppendRuntime_spec_within_reverted
    (bundleBase ret ctl cnt cap rbase : Word)
    (v1 v2 v3 v4 v5 g6 g7 : Word)
    (t0Old t1Old t2Old t3Old : Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Word)
    (hlt : BitVec.ult cnt cap)
    (hstatus : v2 ≠ 0)
    (hrev : BitVec.ult v5 v4) :
    cpsTripleWithin 24 (bundleBase + 112) (ret &&& ~~~1)
      (rrBundleCode bundleBase)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
        (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ m0) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) **
        (.x13 ↦ᵣ v3) ** (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ (0 : Word)) **
        (.x16 ↦ᵣ (0 : Word)) ** (.x17 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ (cnt + 1)) ** (.x6 ↦ᵣ cap) **
        (.x7 ↦ᵣ (rbase + (cnt <<< 6))) ** (.x28 ↦ᵣ (cnt <<< 6)) **
        (ctl ↦ₘ (cnt + 1)) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (cnt <<< 6)) ↦ₘ v1) **
        ((rbase + (cnt <<< 6) + 8) ↦ₘ v2) **
        ((rbase + (cnt <<< 6) + 16) ↦ₘ v3) **
        ((rbase + (cnt <<< 6) + 24) ↦ₘ v4) **
        ((rbase + (cnt <<< 6) + 32) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 40) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 48) ↦ₘ (0 : Word)) **
        ((rbase + (cnt <<< 6) + 56) ↦ₘ (0 : Word))) := by
  set E := bundleBase + 112 with hE
  -- ---- bundle idx 28: beq not taken (v2 ≠ 0) ----
  have hbeq := beq_spec_gen_within .x12 .x0 (16 : BitVec 13) v2 (0 : Word) E
  rw [show (E + 4 : Word) = bundleBase + 116 from by
        rw [hE, BitVec.add_assoc]; rfl] at hbeq
  have hmono28 : ∀ a' i, CodeReq.singleton E
      (.BEQ .x12 .x0 (16 : BitVec 13)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 28 _ E (by rw [hE]; rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hBeq := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono28 hbeq)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hstatus)
  -- ---- bundle idx 29: bltu TAKEN (v5 <u v4) → idx 32 ----
  have hbltu := bltu_spec_gen_within .x15 .x14 (12 : BitVec 13) v5 v4
    (bundleBase + 116)
  rw [show (bundleBase + 116 : Word) + signExtend13 (12 : BitVec 13)
        = bundleBase + 128 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hbltu
  have hmono29 : ∀ a' i, CodeReq.singleton (bundleBase + 116)
      (.BLTU .x15 .x14 (12 : BitVec 13)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 29 _ (bundleBase + 116) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hBltu := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono29 hbltu)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd hrev (((sepConj_pure_right _).1 h_pure).2))
  -- ---- bundle idx 32-35: zero the window and jump into append ----
  have hli5 := li_spec_gen_within .x15 v5 (0 : Word) (bundleBase + 128)
    (by decide)
  have hmono32 : ∀ a' i, CodeReq.singleton (bundleBase + 128)
      (.LI .x15 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 32 _ (bundleBase + 128) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi5 := cpsTripleWithin_extend_code hmono32 hli5
  rw [show (bundleBase + 128 : Word) + 4 = bundleBase + 132 from by
        rw [BitVec.add_assoc]; rfl] at hLi5
  have hli6 := li_spec_gen_within .x16 g6 (0 : Word) (bundleBase + 132)
    (by decide)
  have hmono33 : ∀ a' i, CodeReq.singleton (bundleBase + 132)
      (.LI .x16 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 33 _ (bundleBase + 132) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi6 := cpsTripleWithin_extend_code hmono33 hli6
  rw [show (bundleBase + 132 : Word) + 4 = bundleBase + 136 from by
        rw [BitVec.add_assoc]; rfl] at hLi6
  have hli7 := li_spec_gen_within .x17 g7 (0 : Word) (bundleBase + 136)
    (by decide)
  have hmono34 : ∀ a' i, CodeReq.singleton (bundleBase + 136)
      (.LI .x17 (0 : Word)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 34 _ (bundleBase + 136) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hLi7 := cpsTripleWithin_extend_code hmono34 hli7
  rw [show (bundleBase + 136 : Word) + 4 = bundleBase + 140 from by
        rw [BitVec.add_assoc]; rfl] at hLi7
  have hjmp := jal_x0_spec_gen_within (-108 : BitVec 21) (bundleBase + 140)
  rw [show (bundleBase + 140 : Word) + signExtend21 (-108 : BitVec 21)
        = bundleBase + 32 from by
        rw [show signExtend21 (-108 : BitVec 21)
              = (0xFFFFFFFFFFFFFF94 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hjmp
  have hmono35 : ∀ a' i, CodeReq.singleton (bundleBase + 140)
      (.JAL .x0 (-108 : BitVec 21)) a' = some i →
      rrBundleCode bundleBase a' = some i :=
    rrb_mem bundleBase 35 _ (bundleBase + 140) (by rfl)
      (by rw [rrbProg_len]; omega) (by rfl)
  have hJmp := cpsTripleWithin_extend_code hmono35 hjmp
  have hMid : cpsTripleWithin 4 (bundleBase + 128) (bundleBase + 32)
      (rrBundleCode bundleBase)
      ((.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7))
      ((.x15 ↦ᵣ (0 : Word)) ** (.x16 ↦ᵣ (0 : Word)) **
        (.x17 ↦ᵣ (0 : Word))) := by
    runBlock hLi5 hLi6 hLi7 hJmp
  -- ---- the append callee ----
  have hAppend := receiptRecordsAppend_bundleSpec_ok bundleBase ret ctl cnt
    cap rbase v1 v2 v3 v4 (0 : Word) (0 : Word) (0 : Word)
    t0Old t1Old t2Old t3Old m0 m1 m2 m3 m4 m5 m6 m7 hlt
  -- ---- frame and compose ----
  have hBeqF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x13 ↦ᵣ v3) **
      (.x14 ↦ᵣ v4) ** (.x15 ↦ᵣ v5) ** (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
      (.x1 ↦ᵣ ret) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hBeq
  have hBltuF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
      (.x16 ↦ᵣ g6) ** (.x17 ↦ᵣ g7) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hBltu
  have hMidF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ v1) ** (.x12 ↦ᵣ v2) ** (.x13 ↦ᵣ v3) **
      (.x14 ↦ᵣ v4) **
      (.x1 ↦ᵣ ret) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
      (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 8) ↦ₘ cap) ** ((ctl + 16) ↦ₘ rbase) **
      ((rbase + (cnt <<< 6)) ↦ₘ m0) **
      ((rbase + (cnt <<< 6) + 8) ↦ₘ m1) **
      ((rbase + (cnt <<< 6) + 16) ↦ₘ m2) **
      ((rbase + (cnt <<< 6) + 24) ↦ₘ m3) **
      ((rbase + (cnt <<< 6) + 32) ↦ₘ m4) **
      ((rbase + (cnt <<< 6) + 40) ↦ₘ m5) **
      ((rbase + (cnt <<< 6) + 48) ↦ₘ m6) **
      ((rbase + (cnt <<< 6) + 56) ↦ₘ m7))
    (by pcFree) hMid
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hBeqF hBltuF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hMidF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hAppend
    intro h hp; xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s3

end ReceiptRecordsAppendSpec

end EvmAsm.Codegen
