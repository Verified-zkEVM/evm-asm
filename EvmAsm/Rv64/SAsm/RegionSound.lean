/-
  EvmAsm.Rv64.SAsm.RegionSound

  Soundness of byte loads from the SAsm read-only region: a supported load
  (`LBU`/`LB`) at regFileIs granularity reads exactly the region byte the
  pure engine (`Region.byteAt`) computes, leaving the `bytesRegion`
  assertion untouched.

  The bridge from the dword-packed memory model is
  `holdsFor_bytesRegion_getByte`, built on `bytesRegion_dword_at` and the
  `extractByte`/`packBytes` algebra (EvmAsm.Rv64.MemRegion / ByteOps).
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.Sym
import EvmAsm.Rv64.SAsm.RegFileSep

namespace EvmAsm.Rv64
namespace SAsm

private theorem sepConj_left_comm (A B C : Assertion) :
    (A ** (B ** C)) = (B ** (A ** C)) := by
  rw [← sepConj_assoc', sepConj_comm' A B, sepConj_assoc']

/-- Extract byte `i` of a framed `bytesRegion` from the machine state. -/
theorem holdsFor_bytesRegion_getByte {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {i : Nat} (halign : b.toNat % 8 = 0) (hi : i < bs.length)
    (hover : b.toNat + i < 2 ^ 64) :
    s.getByte (b + BitVec.ofNat 64 i) = bs[i]'hi := by
  obtain ⟨front, rest, hfp, hrp, heq⟩ :=
    bytesRegion_dword_at b bs (i / 8) (by omega)
  rw [heq] at hPR
  have hcell : (((b + BitVec.ofNat 64 (8 * (i / 8))) ↦ₘ
      packBytes ((bs.drop (8 * (i / 8))).take 8))).holdsFor s :=
    holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hmem := (holdsFor_memIs.mp hcell).1
  show extractByte (s.getMem (alignToDword (b + BitVec.ofNat 64 i)))
    (byteOffset (b + BitVec.ofNat 64 i)) = bs[i]'hi
  rw [alignToDword_add_ofNat_of_aligned halign hover,
    byteOffset_add_ofNat_of_aligned halign hover, hmem]
  have hchunk : i % 8 < ((bs.drop (8 * (i / 8))).take 8).length := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [extractByte_packBytes _ (i % 8) (by omega) hchunk]
  rw [List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- `extractWord32` is the little-endian append of its four bytes. -/
theorem extractWord32_eq_append (w : Word) (p : Nat) (hp : p < 2) :
    extractWord32 w p
      = extractByte w (4 * p + 3) ++ extractByte w (4 * p + 2)
        ++ extractByte w (4 * p + 1) ++ extractByte w (4 * p) := by
  interval_cases p <;>
    (apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp only [extractWord32, extractByte, BitVec.getLsbD_append,
       BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
     interval_cases i <;> simp)

/-- Extract the packed cell containing region index `i` from a framed
    `bytesRegion`. -/
theorem holdsFor_bytesRegion_cell {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {i : Nat} (hi : i < bs.length) :
    s.getMem (b + BitVec.ofNat 64 (8 * (i / 8)))
      = packBytes ((bs.drop (8 * (i / 8))).take 8) := by
  obtain ⟨front, rest, -, -, heq⟩ :=
    bytesRegion_dword_at b bs (i / 8) (by omega)
  rw [heq] at hPR
  exact (holdsFor_memIs.mp (holdsFor_sepConj_elim_left
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))).1

/-- Read the aligned dword at region index `i` from a framed `bytesRegion`. -/
theorem holdsFor_bytesRegion_getMem {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {i : Nat} (h8 : 8 ∣ i) (hlen : i < bs.length) :
    s.getMem (b + BitVec.ofNat 64 i) = packBytes ((bs.drop i).take 8) := by
  have h := holdsFor_bytesRegion_cell hPR hlen
  rw [show 8 * (i / 8) = i from by omega] at h
  exact h

/-- Read the aligned little-endian 32-bit word at region index `i` from a
    framed `bytesRegion`. -/
theorem holdsFor_bytesRegion_getWord32 {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {i : Nat} (halign : b.toNat % 8 = 0) (h4 : 4 ∣ i)
    (hlen : i + 4 ≤ bs.length) (hover : b.toNat + i < 2 ^ 64) :
    s.getWord32 (b + BitVec.ofNat 64 i)
      = (bs[i + 3]'(by omega) ++ bs[i + 2]'(by omega)
          ++ bs[i + 1]'(by omega) ++ bs[i]'(by omega) : BitVec 32) := by
  have hcell := holdsFor_bytesRegion_cell hPR (show i < bs.length by omega)
  show extractWord32 (s.getMem (alignToDword (b + BitVec.ofNat 64 i)))
    (byteOffset (b + BitVec.ofNat 64 i) / 4) = _
  rw [alignToDword_add_ofNat_of_aligned halign hover,
    byteOffset_add_ofNat_of_aligned halign hover, hcell,
    extractWord32_eq_append _ _ (by omega)]
  have hchunk : ∀ j, j < 4 →
      4 * (i % 8 / 4) + j < ((bs.drop (8 * (i / 8))).take 8).length := by
    intro j hj
    simp only [List.length_take, List.length_drop]
    omega
  rw [extractByte_packBytes _ _ (by omega) (hchunk 3 (by omega)),
    extractByte_packBytes _ _ (by omega) (hchunk 2 (by omega)),
    extractByte_packBytes _ _ (by omega) (hchunk 1 (by omega)),
    extractByte_packBytes _ (4 * (i % 8 / 4)) (by omega)
      (by simpa using hchunk 0 (by omega))]
  simp only [List.getElem_take, List.getElem_drop]
  rw [getElem_congr_idx
      (show 8 * (i / 8) + (4 * (i % 8 / 4) + 3) = i + 3 from by omega),
    getElem_congr_idx
      (show 8 * (i / 8) + (4 * (i % 8 / 4) + 2) = i + 2 from by omega),
    getElem_congr_idx
      (show 8 * (i / 8) + (4 * (i % 8 / 4) + 1) = i + 1 from by omega),
    getElem_congr_idx
      (show 8 * (i / 8) + 4 * (i % 8 / 4) = i from by omega)]

/-- `extractHalfword` is the little-endian append of its two bytes. -/
theorem extractHalfword_eq_append (w : Word) (p : Nat) (hp : p < 4) :
    extractHalfword w p
      = extractByte w (2 * p + 1) ++ extractByte w (2 * p) := by
  interval_cases p <;>
    (apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp only [extractHalfword, extractByte, BitVec.getLsbD_append,
       BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
     interval_cases i <;> simp)

/-- Read the aligned little-endian halfword at region index `i` from a
    framed `bytesRegion`. -/
theorem holdsFor_bytesRegion_getHalfword {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {i : Nat} (halign : b.toNat % 8 = 0) (h2 : 2 ∣ i)
    (hlen : i + 2 ≤ bs.length) (hover : b.toNat + i < 2 ^ 64) :
    s.getHalfword (b + BitVec.ofNat 64 i)
      = (bs[i + 1]'(by omega) ++ bs[i]'(by omega) : BitVec 16) := by
  have hcell := holdsFor_bytesRegion_cell hPR (show i < bs.length by omega)
  show extractHalfword (s.getMem (alignToDword (b + BitVec.ofNat 64 i)))
    (byteOffset (b + BitVec.ofNat 64 i) / 2) = _
  rw [alignToDword_add_ofNat_of_aligned halign hover,
    byteOffset_add_ofNat_of_aligned halign hover, hcell,
    extractHalfword_eq_append _ _ (by omega)]
  have hchunk : ∀ j, j < 2 →
      2 * (i % 8 / 2) + j < ((bs.drop (8 * (i / 8))).take 8).length := by
    intro j hj
    simp only [List.length_take, List.length_drop]
    omega
  rw [extractByte_packBytes _ _ (by omega) (hchunk 1 (by omega)),
    extractByte_packBytes _ (2 * (i % 8 / 2)) (by omega)
      (by simpa using hchunk 0 (by omega))]
  simp only [List.getElem_take, List.getElem_drop]
  rw [getElem_congr_idx
      (show 8 * (i / 8) + (2 * (i % 8 / 2) + 1) = i + 1 from by omega),
    getElem_congr_idx
      (show 8 * (i / 8) + 2 * (i % 8 / 2) = i from by omega)]

/-- `Region.half16At` at `base + i`, as list elements. -/
theorem half16At_index (reg : Region) {i : Nat}
    (hlen : i + 2 ≤ reg.bytes.length)
    (hover : reg.base.toNat + i + 2 ≤ 2 ^ 64) :
    reg.half16At (reg.base + BitVec.ofNat 64 i)
      = (reg.bytes[i + 1]'(by omega) ++ reg.bytes[i]'(by omega) : BitVec 16) := by
  have hb : ∀ j : Nat, (hj : j < 2) →
      reg.byteAt (reg.base + BitVec.ofNat 64 i + BitVec.ofNat 64 j)
        = reg.bytes[i + j]'(by omega) := by
    intro j hj
    unfold Region.byteAt
    rw [show (reg.base + BitVec.ofNat 64 i + BitVec.ofNat 64 j) - reg.base
        = BitVec.ofNat 64 (i + j) from by bv_omega]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  unfold Region.half16At
  rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl]
  rw [hb 1 (by omega)]
  congr 1
  have := hb 0 (by omega)
  rw [show reg.base + BitVec.ofNat 64 i + BitVec.ofNat 64 0
      = reg.base + BitVec.ofNat 64 i from by bv_omega] at this
  exact this

/-- `Region.word32At` at `base + i`, as list elements. -/
theorem word32At_index (reg : Region) {i : Nat}
    (hlen : i + 4 ≤ reg.bytes.length)
    (hover : reg.base.toNat + i + 4 ≤ 2 ^ 64) :
    reg.word32At (reg.base + BitVec.ofNat 64 i)
      = (reg.bytes[i + 3]'(by omega) ++ reg.bytes[i + 2]'(by omega)
          ++ reg.bytes[i + 1]'(by omega) ++ reg.bytes[i]'(by omega) : BitVec 32) := by
  have hb : ∀ j : Nat, (hj : j < 4) →
      reg.byteAt (reg.base + BitVec.ofNat 64 i + BitVec.ofNat 64 j)
        = reg.bytes[i + j]'(by omega) := by
    intro j hj
    unfold Region.byteAt
    rw [show (reg.base + BitVec.ofNat 64 i + BitVec.ofNat 64 j) - reg.base
        = BitVec.ofNat 64 (i + j) from by bv_omega]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  unfold Region.word32At
  rw [show (3 : Word) = BitVec.ofNat 64 3 from rfl,
    show (2 : Word) = BitVec.ofNat 64 2 from rfl,
    show (1 : Word) = BitVec.ofNat 64 1 from rfl]
  rw [hb 3 (by omega), hb 2 (by omega), hb 1 (by omega)]
  congr 1
  have := hb 0 (by omega)
  rw [show reg.base + BitVec.ofNat 64 i + BitVec.ofNat 64 0
      = reg.base + BitVec.ofNat 64 i from by bv_omega] at this
  exact this

/-- Load spec at register-file granularity: one step, the destination
    receives the value the pure engine computes (`LoadOp.val`), the region
    itself untouched. -/
theorem regFile_load_spec_within (i : Instr) (l : LoadOp) (reg : Region)
    (rf : RegFile) (base : Word)
    (hsem : loadSem i = some l)
    (hreg : reg.wf)
    (hrd : (Reg.isExposed l.rd || l.rd == .x0) = true)
    (hrs1 : (Reg.isExposed l.rs1 || l.rs1 == .x0) = true)
    (hin : reg.loadOk (rf.get l.rs1 + signExtend12 l.ofs) l.nbytes) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base i)
      ((regFileIs rf) ** bytesRegion reg.base reg.bytes)
      ((regFileIs (rf.set l.rd
          (l.val reg (rf.get l.rs1 + signExtend12 l.ofs)))) **
        bytesRegion reg.base reg.bytes) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some i := CodeReq.singleton_satisfiedBy.mp hcr
  rw [sepConj_assoc'] at hPR
  -- hPR : (regFileIs rf ** (bytesRegion ** R)).holdsFor s
  have hrs1v : s.getReg l.rs1 = rf.get l.rs1 :=
    holdsFor_regFileIs_agree hPR hrs1
  have hPR2 : ((bytesRegion reg.base reg.bytes) ** (regFileIs rf ** R)).holdsFor s := by
    rw [sepConj_left_comm] at hPR
    exact hPR
  rw [sepConj_left_comm] at hPR2
  -- shared address facts
  set addr := rf.get l.rs1 + signExtend12 l.ofs with haddr_def
  obtain ⟨hdvd, hlen⟩ := hin
  set i0 := (addr - reg.base).toNat with hi0_def
  have hn : 1 ≤ l.nbytes := by
    cases i <;> simp only [loadSem, reduceCtorEq] at hsem <;>
      (injection hsem with hsem; subst hsem; simp)
  have hi0lt : i0 < reg.bytes.length := by omega
  have haddr_eq : addr = reg.base + BitVec.ofNat 64 i0 := by
    rw [hi0_def]
    bv_omega
  have hover : reg.base.toNat + i0 < 2 ^ 64 := by
    have := hreg.2.1
    omega
  have haddr_toNat : addr.toNat = reg.base.toNat + i0 := by
    rw [haddr_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hvalidmem : isValidMemAddr addr = true := by
    rw [haddr_eq]
    exact hreg.2.2 _ hi0lt
  have hb8 : reg.base.toNat % 8 = 0 := hreg.1
  -- one machine step, ending in the engine's value
  have hkey : step s = some (execInstrBr s i)
      ∧ execInstrBr s i
        = (s.setReg l.rd (l.val reg addr)).setPC (s.pc + 4) := by
    have hPR2' := hPR2
    rw [sepConj_left_comm] at hPR2'
    -- hPR2' : (bytesRegion ** (regFileIs ** R)).holdsFor s
    cases i <;> simp only [loadSem, reduceCtorEq] at hsem
    case LB rd rs1 ofs =>
      injection hsem with hsem; subst hsem
      simp only at hdvd hlen ⊢
      refine ⟨step_lb hfetch (by rw [hrs1v]; simpa using hvalidmem), ?_⟩
      simp only [execInstrBr]
      rw [hrs1v]
      show _ = (s.setReg _ ((reg.byteAt addr).signExtend 64)).setPC _
      rw [show reg.byteAt addr = reg.bytes[i0]'hi0lt from by
        unfold Region.byteAt
        rw [← hi0_def, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi0lt]
        rfl]
      rw [show s.getByte addr = reg.bytes[i0]'hi0lt from by
        conv_lhs => rw [haddr_eq]
        exact holdsFor_bytesRegion_getByte hPR2' hb8 hi0lt hover]
    case LBU rd rs1 ofs =>
      injection hsem with hsem; subst hsem
      simp only at hdvd hlen ⊢
      refine ⟨step_lbu hfetch (by rw [hrs1v]; simpa using hvalidmem), ?_⟩
      simp only [execInstrBr]
      rw [hrs1v]
      show _ = (s.setReg _ ((reg.byteAt addr).zeroExtend 64)).setPC _
      rw [show reg.byteAt addr = reg.bytes[i0]'hi0lt from by
        unfold Region.byteAt
        rw [← hi0_def, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi0lt]
        rfl]
      rw [show s.getByte addr = reg.bytes[i0]'hi0lt from by
        conv_lhs => rw [haddr_eq]
        exact holdsFor_bytesRegion_getByte hPR2' hb8 hi0lt hover]
    case LH rd rs1 ofs =>
      injection hsem with hsem; subst hsem
      simp only at hdvd hlen ⊢
      have hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidHalfwordAccess addr = true
        simp only [isValidHalfwordAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned2_eq, beq_iff_eq]
        omega
      refine ⟨step_lh hfetch hvalid, ?_⟩
      simp only [execInstrBr]
      rw [hrs1v]
      show _ = (s.setReg _ ((reg.half16At addr).signExtend 64)).setPC _
      rw [show s.getHalfword addr = reg.half16At addr from by
        conv_lhs => rw [haddr_eq]
        rw [haddr_eq, half16At_index reg hlen (by have := hreg.2.1; omega)]
        exact holdsFor_bytesRegion_getHalfword hPR2' hb8 hdvd hlen hover]
    case LHU rd rs1 ofs =>
      injection hsem with hsem; subst hsem
      simp only at hdvd hlen ⊢
      have hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidHalfwordAccess addr = true
        simp only [isValidHalfwordAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned2_eq, beq_iff_eq]
        omega
      refine ⟨step_lhu hfetch hvalid, ?_⟩
      simp only [execInstrBr]
      rw [hrs1v]
      show _ = (s.setReg _ ((reg.half16At addr).zeroExtend 64)).setPC _
      rw [show s.getHalfword addr = reg.half16At addr from by
        conv_lhs => rw [haddr_eq]
        rw [haddr_eq, half16At_index reg hlen (by have := hreg.2.1; omega)]
        exact holdsFor_bytesRegion_getHalfword hPR2' hb8 hdvd hlen hover]
    case LW rd rs1 ofs =>
      injection hsem with hsem; subst hsem
      simp only at hdvd hlen ⊢
      have hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidMemAccess addr = true
        simp only [isValidMemAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned4, beq_iff_eq]
        omega
      refine ⟨step_lw hfetch hvalid, ?_⟩
      simp only [execInstrBr]
      rw [hrs1v]
      show _ = (s.setReg _ ((reg.word32At addr).signExtend 64)).setPC _
      rw [show s.getWord32 addr = reg.word32At addr from by
        conv_lhs => rw [haddr_eq]
        rw [haddr_eq, word32At_index reg hlen (by have := hreg.2.1; omega)]
        exact holdsFor_bytesRegion_getWord32 hPR2' hb8 hdvd hlen hover]
    case LWU rd rs1 ofs =>
      injection hsem with hsem; subst hsem
      simp only at hdvd hlen ⊢
      have hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidMemAccess addr = true
        simp only [isValidMemAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned4, beq_iff_eq]
        omega
      refine ⟨step_lwu hfetch hvalid, ?_⟩
      simp only [execInstrBr]
      rw [hrs1v]
      show _ = (s.setReg _ ((reg.word32At addr).zeroExtend 64)).setPC _
      rw [show s.getWord32 addr = reg.word32At addr from by
        conv_lhs => rw [haddr_eq]
        rw [haddr_eq, word32At_index reg hlen (by have := hreg.2.1; omega)]
        exact holdsFor_bytesRegion_getWord32 hPR2' hb8 hdvd hlen hover]
    case LD rd rs1 ofs =>
      injection hsem with hsem; subst hsem
      simp only at hdvd hlen ⊢
      have hvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidDwordAccess addr = true
        simp only [isValidDwordAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned8, beq_iff_eq]
        omega
      refine ⟨step_ld hfetch hvalid, ?_⟩
      simp only [execInstrBr]
      rw [hrs1v]
      show _ = (s.setReg _ (reg.dwordAt addr)).setPC _
      rw [show reg.dwordAt addr = packBytes ((reg.bytes.drop i0).take 8) from rfl]
      rw [show s.getMem addr = packBytes ((reg.bytes.drop i0).take 8) from by
        conv_lhs => rw [haddr_eq]
        exact holdsFor_bytesRegion_getMem hPR2' hdvd hi0lt]
  obtain ⟨hstep', hexec⟩ := hkey
  refine ⟨1, Nat.le_refl 1,
    (s.setReg l.rd (l.val reg addr)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · rcases Bool.or_eq_true_iff.mp hrd with hexp | hx0
    · have h1 := holdsFor_sepConj_regFileIs_setReg
        (v := l.val reg addr) hexp hPR
      rw [← sepConj_assoc'] at h1
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regFileIs _)
          (bytesRegion_pcFree _ _)) hR) h1
    · have hx0' : l.rd = .x0 := by simpa using hx0
      rw [hx0', RegFile.set_x0]
      rw [show s.setReg .x0 (l.val reg addr) = s from rfl]
      rw [← sepConj_assoc'] at hPR
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regFileIs _)
          (bytesRegion_pcFree _ _)) hR) hPR

-- ============================================================================
-- The region-carrying reachable-set embedding
-- ============================================================================

/-- Leaf-shaped embedding of a reachable set: the exposed register file plus
    the function's read-only region. -/
def asrtM (reg : Region) (reach : Reach) : Assertion :=
  asrtOf reach ** bytesRegion reg.base reg.bytes

theorem pcFree_asrtM (reg : Region) (reach : Reach) : (asrtM reg reach).pcFree :=
  pcFree_sepConj (pcFree_asrtOf _) (bytesRegion_pcFree _ _)

theorem asrtM_mono {reg : Region} {r₁ r₂ : Reach} (h : ∀ rf, r₁ rf → r₂ rf) :
    ∀ hp, asrtM reg r₁ hp → asrtM reg r₂ hp :=
  fun hp => sepConj_mono_left (fun hq hh => by
    obtain ⟨rf, hrf, hr⟩ := hh
    exact ⟨rf, hrf, h rf hr⟩) hp

theorem asrtM_unsat {reg : Region} {r : Reach} (h : ∀ rf, r rf → False) :
    ∀ hp, asrtM reg r hp → False := by
  rintro hp ⟨h1, h2, -, -, ⟨rf, -, hr⟩, -⟩
  exact h rf hr

/-- Split an `asrtM` precondition into a per-register-file family with the
    region alongside. -/
theorem cpsTripleWithin_exists_pre_M {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {reg : Region} {reach : Reach} {Q : Assertion}
    (h : ∀ rf, reach rf → cpsTripleWithin n entry exit_ cr
      ((regFileIs rf) ** bytesRegion reg.base reg.bytes) Q) :
    cpsTripleWithin n entry exit_ cr (asrtM reg reach) Q := by
  intro R hR s hcr hPR hpc
  rw [show asrtM reg reach
    = (asrtOf reach ** bytesRegion reg.base reg.bytes) from rfl,
    sepConj_assoc'] at hPR
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, hrf1, hreach⟩, hR2⟩ := hPR
  have hPR' : ((regFileIs rf) ** (bytesRegion reg.base reg.bytes ** R)).holdsFor s :=
    ⟨hp, hcompat, h1, h2, hd, hu, hrf1, hR2⟩
  rw [← sepConj_assoc'] at hPR'
  exact h rf hreach R hR s hcr hPR' hpc

end SAsm
end EvmAsm.Rv64
