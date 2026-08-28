/-
  EvmAsm.Codegen.Programs.ReceiptRecordsSAsm

  Proof-first (DCode) port of the first two entries of the receipt-record
  arena BUNDLE — `receipt_records_init` and `receipt_records_clear` — and
  the first multi-entry bundle statements (#12991): both entries' triples
  are stated over ONE shared `CodeReq` covering the concatenated bundle
  image, so a caller holding the bundle's code needs no per-symbol code
  identity.  The glue is `CodeReq.ofProg_mono_sub` fed to `DCode.retSpec`'s
  `hcode` inclusion parameter — no new soundness machinery.

  The remaining three entries (`receipt_records_append`,
  `receipt_records_append_runtime_result`, `receipt_record_nth`) read the
  control block AND write the separately-pointed record arena, which needs
  two writable regions; the DCode layer owns a single rw window, so they
  stay string-emitted until a dual-region story exists (tracked in #12991).
  `append_runtime_result` additionally tail-jumps INTO
  `receipt_records_append` — the composition that will consume the shared
  bundle `CodeReq` non-trivially.
-/

import EvmAsm.Rv64.SAsm.Deriv
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Codegen.Programs.ReceiptRecordsProgs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

namespace ReceiptRecordsSAsm

/-! ## Byte-splice helpers -/

/-- A full-width splice at offset 0 replaces the buffer. -/
theorem rr_setBytes_full (bs ns : List (BitVec 8))
    (h : ns.length = bs.length) :
    setBytes bs 0 ns = ns := by
  have hslot := setBytes_slot bs ns 0 (by omega)
  simp only [List.drop_zero] at hslot
  have hlen : (setBytes bs 0 ns).length = ns.length := by
    rw [length_setBytes, h]
  have htake : (setBytes bs 0 ns).take ns.length = setBytes bs 0 ns :=
    List.take_of_length_le (Nat.le_of_eq hlen)
  rwa [htake] at hslot

/-- Three adjacent 8-byte splices cover a 24-byte buffer completely, so
    the result is the concatenation — the initial contents drop out. -/
theorem rr_bytes3 (ws0 a b c : List (BitVec 8)) (h : ws0.length = 24)
    (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8) :
    setBytes (setBytes (setBytes ws0 0 a) 8 b) 16 c = a ++ b ++ c := by
  have hchain : setBytes ws0 0 (a ++ b ++ c)
      = setBytes (setBytes (setBytes ws0 0 a) 8 b) 16 c := by
    rw [setBytes_append, setBytes_append]
    simp only [List.length_append, ha, hb, Nat.zero_add]
  rw [← hchain]
  exact rr_setBytes_full ws0 (a ++ b ++ c)
    (by simp only [List.length_append, ha, hb, hc, h])

/-- An `SD` stores the eight little-endian bytes of `rs2` into the window. -/
theorem execInstrRF_sd' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) :
    execInstrRF ro b rf ws (.SD rs1 rs2 ofs)
      = (rf, setBytes ws (rf.get rs1 + signExtend12 ofs - b).toNat
          (dwordBytes (rf.get rs2))) := rfl

/-- An `LI` writes the immediate. -/
theorem execInstrRF_li' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd : Reg) (v : Word) :
    execInstrRF ro b rf ws (.LI rd v) = (rf.set rd v, ws) := rfl

/-! ## receipt_records_init

    `a0` = control block (24 bytes), `a1` = capacity, `a2` = record base.
    Writes `count := 0`, `capacity := a1`, `record base := a2`; returns
    `a0 = 0`. -/

/-- Proof-first arena init: three dword stores and the success return. -/
def rriDeriv (ctl cap rbase : Word) (ws0 : List (BitVec 8)) :
    DCode Region.empty (RwRegion.mk ctl 24)
      (fun rf ws A => rf.get .x10 = ctl ∧ rf.get .x11 = cap ∧
        rf.get .x12 = rbase ∧ ws = ws0 ∧ A = empAssertion)
      (fun rf ws A => rf.get .x10 = 0 ∧
        ws = dwordBytes 0 ++ dwordBytes cap ++ dwordBytes rbase ∧
        A = empAssertion) :=
  DCode.seq
    (DCode.block "init"
      [.SD .x10 .x0 (0 : BitVec 12), .SD .x10 .x11 (8 : BitVec 12),
       .SD .x10 .x12 (16 : BitVec 12), .LI .x10 (0 : Word)]
      (by decide)
      (fun _ rf ws A hlen hpre => by
        obtain ⟨h10, h11, h12, hws, hA⟩ := hpre
        have hws24 : ws.length = 24 := hlen
        have ha0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - ctl).toNat
            = 0 := by
          rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
            from by decide]
          bv_omega
        have ha8 : (rf.get .x10 + signExtend12 (8 : BitVec 12) - ctl).toNat
            = 8 := by
          rw [h10, show signExtend12 (8 : BitVec 12) = (8 : Word)
            from by decide]
          bv_omega
        have ha16 : (rf.get .x10 + signExtend12 (16 : BitVec 12) - ctl).toNat
            = 16 := by
          rw [h10, show signExtend12 (16 : BitVec 12) = (16 : Word)
            from by decide]
          bv_omega
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, trivial, trivial⟩
        · show inRw ctl ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8
          unfold inRw
          rw [ha0, hws24]
          omega
        · show (8 : Nat) ∣ (rf.get .x10 + signExtend12 (0 : BitVec 12)
            - ctl).toNat
          rw [ha0]
          exact Nat.dvd_zero 8
        · show inRw ctl
            (setBytes ws ((rf.get .x10 + signExtend12 (0 : BitVec 12)
              - ctl).toNat) (dwordBytes (rf.get .x0)))
            (rf.get .x10 + signExtend12 (8 : BitVec 12)) 8
          unfold inRw
          rw [ha8, length_setBytes, hws24]
          omega
        · show (8 : Nat) ∣ (rf.get .x10 + signExtend12 (8 : BitVec 12)
            - ctl).toNat
          rw [ha8]
        · show inRw ctl
            (setBytes (setBytes ws ((rf.get .x10
                + signExtend12 (0 : BitVec 12) - ctl).toNat)
              (dwordBytes (rf.get .x0)))
              ((rf.get .x10 + signExtend12 (8 : BitVec 12) - ctl).toNat)
              (dwordBytes (rf.get .x11)))
            (rf.get .x10 + signExtend12 (16 : BitVec 12)) 8
          unfold inRw
          rw [ha16, length_setBytes, length_setBytes, hws24]
        · show (8 : Nat) ∣ (rf.get .x10 + signExtend12 (16 : BitVec 12)
            - ctl).toNat
          rw [ha16]
          exact ⟨2, rfl⟩)
      (by
        rintro rf ws A hlen ⟨h10, h11, h12, hws, hA⟩
        have hws24 : ws.length = 24 := hlen
        simp only [execBlock_cons, execBlock_nil, execInstrRF_sd',
          execInstrRF_li']
        refine ⟨?_, ?_, hA⟩
        · rw [RegFile.get_set_self _ _ _ (by decide)]
        · rw [RegFile.get_x0,
            show (rf.get .x10 + signExtend12 (0 : BitVec 12) - ctl).toNat = 0
              from by
                rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
                  from by decide]
                bv_omega,
            show (rf.get .x10 + signExtend12 (8 : BitVec 12) - ctl).toNat = 8
              from by
                rw [h10, show signExtend12 (8 : BitVec 12) = (8 : Word)
                  from by decide]
                bv_omega,
            show (rf.get .x10 + signExtend12 (16 : BitVec 12) - ctl).toNat = 16
              from by
                rw [h10, show signExtend12 (16 : BitVec 12) = (16 : Word)
                  from by decide]
                bv_omega,
            h11, h12, hws]
          exact rr_bytes3 ws0 (dwordBytes 0) (dwordBytes cap)
            (dwordBytes rbase) (by rw [← hws]; exact hws24)
            (length_dwordBytes 0) (length_dwordBytes cap)
            (length_dwordBytes rbase)))
    (DCode.retJalr "rir")

/-! ## receipt_records_clear

    `a0` = control block; zeroes the count dword only, returns `a0 = 0`. -/

/-- Proof-first arena clear: one dword store and the success return. -/
def rrcDeriv (ctl : Word) (ws0 : List (BitVec 8)) :
    DCode Region.empty (RwRegion.mk ctl 8)
      (fun rf ws A => rf.get .x10 = ctl ∧ ws = ws0 ∧ A = empAssertion)
      (fun rf ws A => rf.get .x10 = 0 ∧ ws = dwordBytes 0 ∧
        A = empAssertion) :=
  DCode.seq
    (DCode.block "clear"
      [.SD .x10 .x0 (0 : BitVec 12), .LI .x10 (0 : Word)]
      (by decide)
      (fun _ rf ws A hlen hpre => by
        obtain ⟨h10, hws, hA⟩ := hpre
        have hws8 : ws.length = 8 := hlen
        have ha0 : (rf.get .x10 + signExtend12 (0 : BitVec 12) - ctl).toNat
            = 0 := by
          rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
            from by decide]
          bv_omega
        refine ⟨⟨?_, ?_⟩, trivial, trivial⟩
        · show inRw ctl ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8
          unfold inRw
          rw [ha0, hws8]
        · show (8 : Nat) ∣ (rf.get .x10 + signExtend12 (0 : BitVec 12)
            - ctl).toNat
          rw [ha0]
          exact Nat.dvd_zero 8)
      (by
        rintro rf ws A hlen ⟨h10, hws, hA⟩
        have hws8 : ws.length = 8 := hlen
        simp only [execBlock_cons, execBlock_nil, execInstrRF_sd',
          execInstrRF_li']
        refine ⟨?_, ?_, hA⟩
        · rw [RegFile.get_set_self _ _ _ (by decide)]
        · rw [RegFile.get_x0,
            show (rf.get .x10 + signExtend12 (0 : BitVec 12) - ctl).toNat = 0
              from by
                rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
                  from by decide]
                bv_omega,
            hws]
          exact rr_setBytes_full ws0 (dwordBytes 0)
            (by rw [length_dwordBytes, ← hws, hws8])))
    (DCode.retJalr "rcr")

/-! ## The generated code -/

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

/-- The generated `receipt_records_init` code. -/
def receiptRecordsInit_prog : Program :=
  (rriDeriv 0 0 0 []).stmt.flatten 0

/-- The generated `receipt_records_clear` code. -/
def receiptRecordsClear_prog : Program :=
  (rrcDeriv 0 []).stmt.flatten 0

-- Pinned instruction sequences (build-time evaluation): byte-identical to
-- the previously hand-written routines.
#guard (receiptRecordsInit_prog : List Instr) ==
    [ .SD .x10 .x0 (0 : BitVec 12),
      .SD .x10 .x11 (8 : BitVec 12),
      .SD .x10 .x12 (16 : BitVec 12),
      .LI .x10 (0 : Word),
      .JALR .x0 .x1 (0 : BitVec 12) ]

#guard (receiptRecordsClear_prog : List Instr) ==
    [ .SD .x10 .x0 (0 : BitVec 12),
      .LI .x10 (0 : Word),
      .JALR .x0 .x1 (0 : BitVec 12) ]

#guard receiptRecordsInit_prog.length = 5
#guard receiptRecordsClear_prog.length = 3

-- The module-side lists `ReceiptRecords.lean` EMITS are exactly the
-- generated programs — the byte tie across the module boundary.
#guard (receiptRecordsInit_prog : List Instr)
    == (receiptRecordsInitProg : List Instr)
#guard (receiptRecordsClear_prog : List Instr)
    == (receiptRecordsClearProg : List Instr)

/-- The code does not depend on the ghost arguments or the base — the
    general statement (the ghosts only enter `Prop` annotations, which
    `flatten` drops), definitional as in `mcDeriv_flatten_ghost_free`. -/
theorem rriDeriv_flatten_ghost_free (ctl cap rbase : Word)
    (ws0 : List (BitVec 8)) (base : Word) :
    (rriDeriv ctl cap rbase ws0).stmt.flatten base
      = (rriDeriv 0 0 0 []).stmt.flatten base := rfl

theorem rrcDeriv_flatten_ghost_free (ctl : Word) (ws0 : List (BitVec 8))
    (base : Word) :
    (rrcDeriv ctl ws0).stmt.flatten base
      = (rrcDeriv 0 []).stmt.flatten base := rfl

/-! ## Per-entry specs over the entry's own code -/

/-- `receipt_records_init`, ra-framed, over its own image. -/
theorem receiptRecordsInit_retSpec (ctl cap rbase : Word)
    (ws0 : List (BitVec 8)) (base ret : Word)
    (hrw : (RwRegion.mk ctl 24).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (rriDeriv ctl cap rbase ws0).stmt.steps base ret
      (CodeReq.ofProg base ((rriDeriv ctl cap rbase ws0).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 24)
          (fun rf ws A => rf.get .x10 = ctl ∧ rf.get .x11 = cap ∧
            rf.get .x12 = rbase ∧ ws = ws0 ∧ A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 24)
          (fun rf ws A => rf.get .x10 = 0 ∧
            ws = dwordBytes 0 ++ dwordBytes cap ++ dwordBytes rbase ∧
            A = empAssertion)) :=
  DCode.retSpec (rriDeriv ctl cap rbase ws0) base ret
    Region.empty_wf hrw halign (fun _ _ h => h)

/-- `receipt_records_clear`, ra-framed, over its own image. -/
theorem receiptRecordsClear_retSpec (ctl : Word) (ws0 : List (BitVec 8))
    (base ret : Word)
    (hrw : (RwRegion.mk ctl 8).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (rrcDeriv ctl ws0).stmt.steps base ret
      (CodeReq.ofProg base ((rrcDeriv ctl ws0).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 8)
          (fun rf ws A => rf.get .x10 = ctl ∧ ws = ws0 ∧
            A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 8)
          (fun rf ws A => rf.get .x10 = 0 ∧ ws = dwordBytes 0 ∧
            A = empAssertion)) :=
  DCode.retSpec (rrcDeriv ctl ws0) base ret
    Region.empty_wf hrw halign (fun _ _ h => h)

/-! ## The bundle: both entries over ONE shared CodeReq (#12991)

    The emitted unit places `receipt_records_clear` immediately after
    `receipt_records_init`; the bundle program is their concatenation and
    each entry's triple lifts to `CodeReq.ofProg bundleBase rrBundleProg`
    via `CodeReq.ofProg_mono_sub` — a caller that owns the bundle image
    once can invoke either entry with no further code-identity argument. -/

/-- The ported prefix of the receipt-record bundle. -/
def rrBundleProg : Program :=
  (receiptRecordsInit_prog : List Instr)
    ++ (receiptRecordsClear_prog : List Instr)

#guard (rrBundleProg : List Instr).length = 8

/-- Instruction offset of `receipt_records_clear` inside the bundle. -/
def rrClearIdx : Nat := 5

/-- `receipt_records_init` over the shared bundle image (entry = base). -/
theorem receiptRecordsInit_bundleSpec (ctl cap rbase : Word)
    (ws0 : List (BitVec 8)) (bundleBase ret : Word)
    (hrw : (RwRegion.mk ctl 24).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (rriDeriv ctl cap rbase ws0).stmt.steps bundleBase ret
      (CodeReq.ofProg bundleBase rrBundleProg)
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 24)
          (fun rf ws A => rf.get .x10 = ctl ∧ rf.get .x11 = cap ∧
            rf.get .x12 = rbase ∧ ws = ws0 ∧ A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 24)
          (fun rf ws A => rf.get .x10 = 0 ∧
            ws = dwordBytes 0 ++ dwordBytes cap ++ dwordBytes rbase ∧
            A = empAssertion)) :=
  DCode.retSpec (rriDeriv ctl cap rbase ws0) bundleBase ret
    Region.empty_wf hrw halign
    (fun a i h =>
      CodeReq.ofProg_mono_sub bundleBase bundleBase
        (rrBundleProg : List Instr)
        (receiptRecordsInit_prog : List Instr) 0
        (by rw [Nat.mul_zero]; exact (BitVec.add_zero _).symm)
        (by decide) (by decide) (by decide) a i
        ((show (rriDeriv ctl cap rbase ws0).stmt.flatten bundleBase
            = (receiptRecordsInit_prog : List Instr) from rfl) ▸ h))

/-- `receipt_records_clear` over the shared bundle image
    (entry = base + 4·`rrClearIdx`). -/
theorem receiptRecordsClear_bundleSpec (ctl : Word) (ws0 : List (BitVec 8))
    (bundleBase ret : Word)
    (hrw : (RwRegion.mk ctl 8).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (rrcDeriv ctl ws0).stmt.steps
      (bundleBase + BitVec.ofNat 64 (4 * rrClearIdx)) ret
      (CodeReq.ofProg bundleBase rrBundleProg)
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 8)
          (fun rf ws A => rf.get .x10 = ctl ∧ ws = ws0 ∧
            A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty (RwRegion.mk ctl 8)
          (fun rf ws A => rf.get .x10 = 0 ∧ ws = dwordBytes 0 ∧
            A = empAssertion)) :=
  DCode.retSpec (rrcDeriv ctl ws0)
    (bundleBase + BitVec.ofNat 64 (4 * rrClearIdx)) ret
    Region.empty_wf hrw halign
    (fun a i h =>
      CodeReq.ofProg_mono_sub bundleBase
        (bundleBase + BitVec.ofNat 64 (4 * rrClearIdx))
        (rrBundleProg : List Instr)
        (receiptRecordsClear_prog : List Instr) rrClearIdx
        rfl (by decide) (by decide) (by decide) a i
        ((show (rrcDeriv ctl ws0).stmt.flatten
              (bundleBase + BitVec.ofNat 64 (4 * rrClearIdx))
            = (receiptRecordsClear_prog : List Instr) from rfl) ▸ h))

end ReceiptRecordsSAsm

end EvmAsm.Codegen
