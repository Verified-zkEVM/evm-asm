/-
  EvmAsm.Codegen.Programs.ReceiptRecordNthSpec

  Flat-layer whole-routine triples for `receipt_record_nth`, the read-side
  counterpart of `receipt_records_append` (see
  `ReceiptRecordsAppendSpec.lean` for the layering rationale — the control
  block and the two 64-byte windows are `**`-separated dword cells, which
  the single-`RwRegion` DCode layer cannot carry).

  Both arms: `receiptRecordNth_spec_within_ok` (index in range: the eight
  record dwords are copied to the output buffer, `a0 = 0`) and
  `receiptRecordNth_spec_within_oob` (index out of range: nothing is
  written, `a0 = 1`).

  Instruction indices (into `receiptRecordNthProg`, entry `base`):
    0     ld t0 (count)
    1     bgeu a1, t0, +88 (→ index 23, the out-of-bounds tail)
    2-4   ld t1 (record base); slli t2, a1, 6; add t1, t1, t2
    5-20  eight ld/sd pairs copying the record to the output buffer
    21-22 li a0, 0; ret
    23-24 li a0, 1; ret
-/

import EvmAsm.Codegen.Programs.ReceiptRecordsProgs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen

namespace ReceiptRecordNthSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The routine's own image at `base`. -/
abbrev rrnCode (base : Word) : CodeReq :=
  CodeReq.ofProg base receiptRecordNthProg

private theorem rrnProg_len :
    (receiptRecordNthProg : List Instr).length = 25 := by decide

private theorem rrnProg_bound :
    4 * (receiptRecordNthProg : List Instr).length < 2 ^ 64 := by
  rw [rrnProg_len]; norm_num

private theorem rrn_mem (base : Word) (k : Nat) (ins : Instr) (A : Word)
    (hA : A = base + BitVec.ofNat 64 (4 * k))
    (hk : k < (receiptRecordNthProg : List Instr).length)
    (hins : (receiptRecordNthProg : List Instr)[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → rrnCode base a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at base A receiptRecordNthProg k ins hA hk hins
      rrnProg_bound a i h

set_option maxRecDepth 8000 in
/-- **`receipt_record_nth`, in-range arm** (`idx <ᵤ cnt`): the eight
    dwords of record `idx` are copied to the output buffer, `a0 = 0`;
    the record itself is untouched. -/
theorem receiptRecordNth_spec_within_ok
    (base ret ctl idx cnt rbase out : Word)
    (t0Old t1Old t2Old t3Old : Word)
    (r0 r1 r2 r3 r4 r5 r6 r7 : Word)
    (o0 o1 o2 o3 o4 o5 o6 o7 : Word)
    (hidx : BitVec.ult idx cnt) :
    cpsTripleWithin 23 base (ret &&& ~~~1) (rrnCode base)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ idx) ** (.x12 ↦ᵣ out) **
        (.x1 ↦ᵣ ret) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        (.x28 ↦ᵣ t3Old) **
        (ctl ↦ₘ cnt) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (idx <<< 6)) ↦ₘ r0) **
        ((rbase + (idx <<< 6) + 8) ↦ₘ r1) **
        ((rbase + (idx <<< 6) + 16) ↦ₘ r2) **
        ((rbase + (idx <<< 6) + 24) ↦ₘ r3) **
        ((rbase + (idx <<< 6) + 32) ↦ₘ r4) **
        ((rbase + (idx <<< 6) + 40) ↦ₘ r5) **
        ((rbase + (idx <<< 6) + 48) ↦ₘ r6) **
        ((rbase + (idx <<< 6) + 56) ↦ₘ r7) **
        (out ↦ₘ o0) ** ((out + 8) ↦ₘ o1) ** ((out + 16) ↦ₘ o2) **
        ((out + 24) ↦ₘ o3) ** ((out + 32) ↦ₘ o4) ** ((out + 40) ↦ₘ o5) **
        ((out + 48) ↦ₘ o6) ** ((out + 56) ↦ₘ o7))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ idx) ** (.x12 ↦ᵣ out) **
        (.x1 ↦ᵣ ret) **
        (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ (rbase + (idx <<< 6))) **
        (.x7 ↦ᵣ (idx <<< 6)) ** (.x28 ↦ᵣ r7) **
        (ctl ↦ₘ cnt) ** ((ctl + 16) ↦ₘ rbase) **
        ((rbase + (idx <<< 6)) ↦ₘ r0) **
        ((rbase + (idx <<< 6) + 8) ↦ₘ r1) **
        ((rbase + (idx <<< 6) + 16) ↦ₘ r2) **
        ((rbase + (idx <<< 6) + 24) ↦ₘ r3) **
        ((rbase + (idx <<< 6) + 32) ↦ₘ r4) **
        ((rbase + (idx <<< 6) + 40) ↦ₘ r5) **
        ((rbase + (idx <<< 6) + 48) ↦ₘ r6) **
        ((rbase + (idx <<< 6) + 56) ↦ₘ r7) **
        (out ↦ₘ r0) ** ((out + 8) ↦ₘ r1) ** ((out + 16) ↦ₘ r2) **
        ((out + 24) ↦ₘ r3) ** ((out + 32) ↦ₘ r4) ** ((out + 40) ↦ₘ r5) **
        ((out + 48) ↦ₘ r6) ** ((out + 56) ↦ₘ r7)) := by
  set slot := rbase + (idx <<< 6) with hslot
  -- ---- idx 0: load count ----
  have hld0 := ld_spec_gen_within .x5 .x10 ctl t0Old cnt (0 : BitVec 12)
    base (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ctl + (0 : Word) = ctl from by bv_omega] at hld0
  have hmono0 : ∀ a' i, CodeReq.singleton base
      (.LD .x5 .x10 (0 : BitVec 12)) a' = some i → rrnCode base a' = some i :=
    rrn_mem base 0 _ base (by rw [show (4 * 0 : Nat) = 0 from rfl]; bv_omega)
      (by rw [rrnProg_len]; omega) (by rfl)
  have hLd0 := cpsTripleWithin_extend_code hmono0 hld0
  -- ---- idx 1: bgeu a1, t0, +88 not taken (idx <u cnt) ----
  have hbgeu := bgeu_spec_gen_within .x11 .x5 (88 : BitVec 13) idx cnt (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by
        rw [BitVec.add_assoc]; rfl] at hbgeu
  have hmono1 : ∀ a' i, CodeReq.singleton (base + 4)
      (.BGEU .x11 .x5 (88 : BitVec 13)) a' = some i →
      rrnCode base a' = some i :=
    rrn_mem base 1 _ (base + 4) (by rw [show (4 * 1 : Nat) = 4 from rfl]; rfl)
      (by rw [rrnProg_len]; omega) (by rfl)
  have hBr := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono1 hbgeu)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd hidx (((sepConj_pure_right _).1 h_pure).2))
  -- ---- idx 2-4: record base, slot offset, slot pointer ----
  have hld1 := ld_spec_gen_within .x6 .x10 ctl t1Old rbase (16 : BitVec 12)
    (base + 8) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hld1
  have hslli := slli_spec_gen_within .x7 .x11 t2Old idx (6 : BitVec 6)
    (base + 12) (by decide)
  rw [show BitVec.toNat (6 : BitVec 6) = 6 from by decide] at hslli
  have hadd := add_spec_gen_rd_eq_rs1_within .x6 .x7 rbase (idx <<< 6)
    (base + 16) (by decide)
  rw [← hslot] at hadd
  have hAddr : cpsTripleWithin 3 (base + 8) (base + 20) (rrnCode base)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ idx) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
        ((ctl + 16) ↦ₘ rbase))
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ idx) ** (.x6 ↦ᵣ slot) **
        (.x7 ↦ᵣ (idx <<< 6)) ** ((ctl + 16) ↦ₘ rbase)) := by
    runBlock hld1 hslli hadd
  -- ---- idx 5-20: eight ld/sd copy pairs ----
  have hcl0 := ld_spec_gen_within .x28 .x6 slot t3Old r0 (0 : BitVec 12)
    (base + 20) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show slot + (0 : Word) = slot from by bv_omega] at hcl0
  have hcs0 := sd_spec_gen_within .x12 .x28 out r0 o0 (0 : BitVec 12)
    (base + 24)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show out + (0 : Word) = out from by bv_omega] at hcs0
  have hcl1 := ld_spec_gen_within .x28 .x6 slot r0 r1 (8 : BitVec 12)
    (base + 28) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hcl1
  have hcs1 := sd_spec_gen_within .x12 .x28 out r1 o1 (8 : BitVec 12)
    (base + 32)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hcs1
  have hcl2 := ld_spec_gen_within .x28 .x6 slot r1 r2 (16 : BitVec 12)
    (base + 36) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hcl2
  have hcs2 := sd_spec_gen_within .x12 .x28 out r2 o2 (16 : BitVec 12)
    (base + 40)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hcs2
  have hcl3 := ld_spec_gen_within .x28 .x6 slot r2 r3 (24 : BitVec 12)
    (base + 44) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at hcl3
  have hcs3 := sd_spec_gen_within .x12 .x28 out r3 o3 (24 : BitVec 12)
    (base + 48)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at hcs3
  have hcl4 := ld_spec_gen_within .x28 .x6 slot r3 r4 (32 : BitVec 12)
    (base + 52) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at hcl4
  have hcs4 := sd_spec_gen_within .x12 .x28 out r4 o4 (32 : BitVec 12)
    (base + 56)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at hcs4
  have hcl5 := ld_spec_gen_within .x28 .x6 slot r4 r5 (40 : BitVec 12)
    (base + 60) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at hcl5
  have hcs5 := sd_spec_gen_within .x12 .x28 out r5 o5 (40 : BitVec 12)
    (base + 64)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at hcs5
  have hcl6 := ld_spec_gen_within .x28 .x6 slot r5 r6 (48 : BitVec 12)
    (base + 68) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at hcl6
  have hcs6 := sd_spec_gen_within .x12 .x28 out r6 o6 (48 : BitVec 12)
    (base + 72)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at hcs6
  have hcl7 := ld_spec_gen_within .x28 .x6 slot r6 r7 (56 : BitVec 12)
    (base + 76) (by decide)
  rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide] at hcl7
  have hcs7 := sd_spec_gen_within .x12 .x28 out r7 o7 (56 : BitVec 12)
    (base + 80)
  rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide] at hcs7
  -- ---- idx 21: li a0, 0 ----
  have hli := li_spec_gen_within .x10 ctl (0 : Word) (base + 84) (by decide)
  have hCopy : cpsTripleWithin 17 (base + 20) (base + 88) (rrnCode base)
      ((.x10 ↦ᵣ ctl) ** (.x6 ↦ᵣ slot) ** (.x12 ↦ᵣ out) ** (.x28 ↦ᵣ t3Old) **
        (slot ↦ₘ r0) ** ((slot + 8) ↦ₘ r1) ** ((slot + 16) ↦ₘ r2) **
        ((slot + 24) ↦ₘ r3) ** ((slot + 32) ↦ₘ r4) ** ((slot + 40) ↦ₘ r5) **
        ((slot + 48) ↦ₘ r6) ** ((slot + 56) ↦ₘ r7) **
        (out ↦ₘ o0) ** ((out + 8) ↦ₘ o1) ** ((out + 16) ↦ₘ o2) **
        ((out + 24) ↦ₘ o3) ** ((out + 32) ↦ₘ o4) ** ((out + 40) ↦ₘ o5) **
        ((out + 48) ↦ₘ o6) ** ((out + 56) ↦ₘ o7))
      ((.x10 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ slot) ** (.x12 ↦ᵣ out) **
        (.x28 ↦ᵣ r7) **
        (slot ↦ₘ r0) ** ((slot + 8) ↦ₘ r1) ** ((slot + 16) ↦ₘ r2) **
        ((slot + 24) ↦ₘ r3) ** ((slot + 32) ↦ₘ r4) ** ((slot + 40) ↦ₘ r5) **
        ((slot + 48) ↦ₘ r6) ** ((slot + 56) ↦ₘ r7) **
        (out ↦ₘ r0) ** ((out + 8) ↦ₘ r1) ** ((out + 16) ↦ₘ r2) **
        ((out + 24) ↦ₘ r3) ** ((out + 32) ↦ₘ r4) ** ((out + 40) ↦ₘ r5) **
        ((out + 48) ↦ₘ r6) ** ((out + 56) ↦ₘ r7)) := by
    runBlock hcl0 hcs0 hcl1 hcs1 hcl2 hcs2 hcl3 hcs3 hcl4 hcs4 hcl5 hcs5
      hcl6 hcs6 hcl7 hcs7 hli
  -- ---- idx 22: ret ----
  have hret := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (base + 88)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (ret + 0 : Word) = ret from by bv_omega] at hret
  have hmono22 : ∀ a' i, CodeReq.singleton (base + 88)
      (.JALR .x0 .x1 (0 : BitVec 12)) a' = some i →
      rrnCode base a' = some i :=
    rrn_mem base 22 _ (base + 88)
      (by rw [show (4 * 22 : Nat) = 88 from rfl]; rfl)
      (by rw [rrnProg_len]; omega) (by rfl)
  have hRet := cpsTripleWithin_extend_code hmono22 hret
  -- ---- frame and compose ----
  have hLd0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ idx) ** (.x12 ↦ᵣ out) ** (.x1 ↦ᵣ ret) **
      (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      ((ctl + 16) ↦ₘ rbase) **
      (slot ↦ₘ r0) ** ((slot + 8) ↦ₘ r1) ** ((slot + 16) ↦ₘ r2) **
      ((slot + 24) ↦ₘ r3) ** ((slot + 32) ↦ₘ r4) ** ((slot + 40) ↦ₘ r5) **
      ((slot + 48) ↦ₘ r6) ** ((slot + 56) ↦ₘ r7) **
      (out ↦ₘ o0) ** ((out + 8) ↦ₘ o1) ** ((out + 16) ↦ₘ o2) **
      ((out + 24) ↦ₘ o3) ** ((out + 32) ↦ₘ o4) ** ((out + 40) ↦ₘ o5) **
      ((out + 48) ↦ₘ o6) ** ((out + 56) ↦ₘ o7))
    (by pcFree) hLd0
  have hBrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x12 ↦ᵣ out) ** (.x1 ↦ᵣ ret) **
      (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) ** ((ctl + 16) ↦ₘ rbase) **
      (slot ↦ₘ r0) ** ((slot + 8) ↦ₘ r1) ** ((slot + 16) ↦ₘ r2) **
      ((slot + 24) ↦ₘ r3) ** ((slot + 32) ↦ₘ r4) ** ((slot + 40) ↦ₘ r5) **
      ((slot + 48) ↦ₘ r6) ** ((slot + 56) ↦ₘ r7) **
      (out ↦ₘ o0) ** ((out + 8) ↦ₘ o1) ** ((out + 16) ↦ₘ o2) **
      ((out + 24) ↦ₘ o3) ** ((out + 32) ↦ₘ o4) ** ((out + 40) ↦ₘ o5) **
      ((out + 48) ↦ₘ o6) ** ((out + 56) ↦ₘ o7))
    (by pcFree) hBr
  have hAddrF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ out) ** (.x1 ↦ᵣ ret) ** (.x5 ↦ᵣ cnt) ** (.x28 ↦ᵣ t3Old) **
      (ctl ↦ₘ cnt) **
      (slot ↦ₘ r0) ** ((slot + 8) ↦ₘ r1) ** ((slot + 16) ↦ₘ r2) **
      ((slot + 24) ↦ₘ r3) ** ((slot + 32) ↦ₘ r4) ** ((slot + 40) ↦ₘ r5) **
      ((slot + 48) ↦ₘ r6) ** ((slot + 56) ↦ₘ r7) **
      (out ↦ₘ o0) ** ((out + 8) ↦ₘ o1) ** ((out + 16) ↦ₘ o2) **
      ((out + 24) ↦ₘ o3) ** ((out + 32) ↦ₘ o4) ** ((out + 40) ↦ₘ o5) **
      ((out + 48) ↦ₘ o6) ** ((out + 56) ↦ₘ o7))
    (by pcFree) hAddr
  have hCopyF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ idx) ** (.x1 ↦ᵣ ret) ** (.x5 ↦ᵣ cnt) **
      (.x7 ↦ᵣ (idx <<< 6)) **
      (ctl ↦ₘ cnt) ** ((ctl + 16) ↦ₘ rbase))
    (by pcFree) hCopy
  have hRetF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ idx) ** (.x12 ↦ᵣ out) **
      (.x5 ↦ᵣ cnt) ** (.x6 ↦ᵣ slot) ** (.x7 ↦ᵣ (idx <<< 6)) **
      (.x28 ↦ᵣ r7) **
      (ctl ↦ₘ cnt) ** ((ctl + 16) ↦ₘ rbase) **
      (slot ↦ₘ r0) ** ((slot + 8) ↦ₘ r1) ** ((slot + 16) ↦ₘ r2) **
      ((slot + 24) ↦ₘ r3) ** ((slot + 32) ↦ₘ r4) ** ((slot + 40) ↦ₘ r5) **
      ((slot + 48) ↦ₘ r6) ** ((slot + 56) ↦ₘ r7) **
      (out ↦ₘ r0) ** ((out + 8) ↦ₘ r1) ** ((out + 16) ↦ₘ r2) **
      ((out + 24) ↦ₘ r3) ** ((out + 32) ↦ₘ r4) ** ((out + 40) ↦ₘ r5) **
      ((out + 48) ↦ₘ r6) ** ((out + 56) ↦ₘ r7))
    (by pcFree) hRet
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hLd0F hBrF
    intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hAddrF
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hCopyF
    intro h hp; xperm_hyp hp
  have s4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s3 hRetF
    intro h hp; xperm_hyp hp
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) s4

set_option maxRecDepth 8000 in
/-- **`receipt_record_nth`, out-of-bounds arm** (`¬ idx <ᵤ cnt`):
    nothing is written and `a0 = 1`. -/
theorem receiptRecordNth_spec_within_oob
    (base ret ctl idx cnt : Word)
    (t0Old : Word)
    (hge : ¬ BitVec.ult idx cnt) :
    cpsTripleWithin 4 base (ret &&& ~~~1) (rrnCode base)
      ((.x10 ↦ᵣ ctl) ** (.x11 ↦ᵣ idx) ** (.x1 ↦ᵣ ret) **
        (.x5 ↦ᵣ t0Old) ** (ctl ↦ₘ cnt))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ idx) ** (.x1 ↦ᵣ ret) **
        (.x5 ↦ᵣ cnt) ** (ctl ↦ₘ cnt)) := by
  -- ---- idx 0: load count ----
  have hld0 := ld_spec_gen_within .x5 .x10 ctl t0Old cnt (0 : BitVec 12)
    base (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ctl + (0 : Word) = ctl from by bv_omega] at hld0
  have hmono0 : ∀ a' i, CodeReq.singleton base
      (.LD .x5 .x10 (0 : BitVec 12)) a' = some i → rrnCode base a' = some i :=
    rrn_mem base 0 _ base (by rw [show (4 * 0 : Nat) = 0 from rfl]; bv_omega)
      (by rw [rrnProg_len]; omega) (by rfl)
  have hLd0 := cpsTripleWithin_extend_code hmono0 hld0
  -- ---- idx 1: bgeu a1, t0, +88 TAKEN → base + 92 ----
  have hbgeu := bgeu_spec_gen_within .x11 .x5 (88 : BitVec 13) idx cnt (base + 4)
  rw [show (base + 4 : Word) + signExtend13 (88 : BitVec 13) = base + 92
        from by
        rw [show signExtend13 (88 : BitVec 13) = (88 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hbgeu
  have hmono1 : ∀ a' i, CodeReq.singleton (base + 4)
      (.BGEU .x11 .x5 (88 : BitVec 13)) a' = some i →
      rrnCode base a' = some i :=
    rrn_mem base 1 _ (base + 4) (by rw [show (4 * 1 : Nat) = 4 from rfl]; rfl)
      (by rw [rrnProg_len]; omega) (by rfl)
  have hBr := cpsBranchWithin_takenPath
    (cpsBranchWithin_extend_code hmono1 hbgeu)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQf
      exact absurd (((sepConj_pure_right _).1 h_pure).2) hge)
  -- ---- idx 23: li a0, 1 ; idx 24: ret ----
  have hli := li_spec_gen_within .x10 ctl (1 : Word) (base + 92) (by decide)
  have hmono23 : ∀ a' i, CodeReq.singleton (base + 92)
      (.LI .x10 (1 : Word)) a' = some i → rrnCode base a' = some i :=
    rrn_mem base 23 _ (base + 92)
      (by rw [show (4 * 23 : Nat) = 92 from rfl]; rfl)
      (by rw [rrnProg_len]; omega) (by rfl)
  have hLi := cpsTripleWithin_extend_code hmono23 hli
  rw [show (base + 92 : Word) + 4 = base + 96 from by
        rw [BitVec.add_assoc]; rfl] at hLi
  have hret := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (base + 96)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (ret + 0 : Word) = ret from by bv_omega] at hret
  have hmono24 : ∀ a' i, CodeReq.singleton (base + 96)
      (.JALR .x0 .x1 (0 : BitVec 12)) a' = some i →
      rrnCode base a' = some i :=
    rrn_mem base 24 _ (base + 96)
      (by rw [show (4 * 24 : Nat) = 96 from rfl]; rfl)
      (by rw [rrnProg_len]; omega) (by rfl)
  have hRet := cpsTripleWithin_extend_code hmono24 hret
  -- ---- frame and compose ----
  have hLd0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ idx) ** (.x1 ↦ᵣ ret))
    (by pcFree) hLd0
  have hBrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ctl) ** (.x1 ↦ᵣ ret) ** (ctl ↦ₘ cnt))
    (by pcFree) hBr
  have hLiF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ idx) ** (.x1 ↦ᵣ ret) ** (.x5 ↦ᵣ cnt) ** (ctl ↦ₘ cnt))
    (by pcFree) hLi
  have hRetF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ idx) ** (.x5 ↦ᵣ cnt) **
      (ctl ↦ₘ cnt))
    (by pcFree) hRet
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hLd0F hBrF
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

end ReceiptRecordNthSpec

end EvmAsm.Codegen
