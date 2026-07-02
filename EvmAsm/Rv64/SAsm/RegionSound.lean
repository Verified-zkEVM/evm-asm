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
import EvmAsm.Rv64.HalfwordOps
import EvmAsm.Rv64.WordOps
import EvmAsm.Rv64.SAsm.Sym
import EvmAsm.Rv64.SAsm.RegFileSep

namespace EvmAsm.Rv64
namespace SAsm

theorem sepConj_left_comm (A B C : Assertion) :
    (A ** (B ** C)) = (B ** (A ** C)) := by
  rw [← sepConj_assoc', sepConj_comm' A B, sepConj_assoc']


theorem sc_assoc_l {A B C : Assertion} :
    ∀ hp, (A ** (B ** C)) hp → ((A ** B) ** C) hp := by
  intro hp h
  rw [sepConj_assoc']
  exact h

theorem sc_assoc_r {A B C : Assertion} :
    ∀ hp, ((A ** B) ** C) hp → (A ** (B ** C)) hp := by
  intro hp h
  rw [← sepConj_assoc']
  exact h

theorem sc_to_swap {A B C : Assertion} :
    ∀ hp, (A ** (B ** C)) hp → ((A ** C) ** B) hp := by
  intro hp h
  rw [sepConj_left_comm A B C, sepConj_comm' B] at h
  exact h

theorem sc_from_swap {A B C : Assertion} :
    ∀ hp, ((A ** C) ** B) hp → (A ** (B ** C)) hp := by
  intro hp h
  rw [sepConj_comm' _ B, sepConj_left_comm B A C] at h
  exact h

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

/-- Update the dword cell containing a spliced store: a framed `bytesRegion`
    moves to the spliced byte list when the machine overwrites that cell with
    the correspondingly spliced packed value. -/
theorem holdsFor_bytesRegion_setBytes {b : Word} {ws ns : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b ws) ** R).holdsFor s)
    {i : Nat} (hns : ns ≠ []) (hr : i % 8 + ns.length ≤ 8)
    (hi : i + ns.length ≤ ws.length) :
    ((bytesRegion b (setBytes ws i ns)) ** R).holdsFor
      (s.setMem (b + BitVec.ofNat 64 (8 * (i / 8)))
        (packBytes (setBytes ((ws.drop (8 * (i / 8))).take 8) (i % 8) ns))) := by
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegion_dword_at_setBytes b ws ns (i / 8) (i % 8) hns hr
      (by have := Nat.div_add_mod i 8; omega)
  rw [show 8 * (i / 8) + i % 8 = i from Nat.div_add_mod i 8] at heqset
  rw [heq] at hPR
  rw [heqset]
  set C := ((b + BitVec.ofNat 64 (8 * (i / 8))) ↦ₘ
    packBytes ((ws.drop (8 * (i / 8))).take 8)) with hC
  set C' := ((b + BitVec.ofNat 64 (8 * (i / 8))) ↦ₘ
    packBytes (setBytes ((ws.drop (8 * (i / 8))).take 8) (i % 8) ns)) with hC'
  rw [sepConj_assoc' front (C ** rest) R,
    sepConj_assoc' C rest R,
    sepConj_left_comm front C (rest ** R)] at hPR
  have hupd := holdsFor_sepConj_memIs_setMem
    (v' := packBytes (setBytes ((ws.drop (8 * (i / 8))).take 8) (i % 8) ns)) hPR
  rw [← hC'] at hupd
  rw [sepConj_assoc' front (C' ** rest) R,
    sepConj_assoc' C' rest R,
    sepConj_left_comm front C' (rest ** R)]
  exact hupd

/-- Store spec at register-file granularity: one step, the writable region's
    bytes move to the spliced payload, the register file untouched.  `hwf` is
    well-formedness of the *current* contents viewed as a region (derived
    from `RwRegion.wf` + the length invariant at the call site). -/
theorem regFile_store_spec_within (i : Instr) (st : StoreOp) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (base : Word)
    (hsem : storeSem i = some st)
    (hwf : (Region.mk rwBase ws).wf)
    (hrs1 : (Reg.isExposed st.rs1 || st.rs1 == .x0) = true)
    (hrs2 : (Reg.isExposed st.rs2 || st.rs2 == .x0) = true)
    (hin : inRw rwBase ws (rf.get st.rs1 + signExtend12 st.ofs) st.nbytes)
    (hdvd : st.nbytes ∣ ((rf.get st.rs1 + signExtend12 st.ofs) - rwBase).toNat) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base i)
      ((regFileIs rf) ** bytesRegion rwBase ws)
      ((regFileIs rf) ** bytesRegion rwBase
        (setBytes ws ((rf.get st.rs1 + signExtend12 st.ofs) - rwBase).toNat
          (st.payload (rf.get st.rs2)))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some i := CodeReq.singleton_satisfiedBy.mp hcr
  rw [sepConj_assoc'] at hPR
  -- hPR : (regFileIs rf ** (bytesRegion ** R)).holdsFor s
  have hrs1v : s.getReg st.rs1 = rf.get st.rs1 :=
    holdsFor_regFileIs_agree hPR hrs1
  have hrs2v : s.getReg st.rs2 = rf.get st.rs2 :=
    holdsFor_regFileIs_agree hPR hrs2
  have hPR2 : ((bytesRegion rwBase ws) ** (regFileIs rf ** R)).holdsFor s := by
    rw [sepConj_left_comm] at hPR
    exact hPR
  set addr := rf.get st.rs1 + signExtend12 st.ofs with haddr_def
  set v := rf.get st.rs2 with hv_def
  unfold inRw at hin
  set i0 := (addr - rwBase).toNat with hi0_def
  have hn : 1 ≤ st.nbytes := storeSem_nbytes_pos hsem
  have hplen : (st.payload v).length = st.nbytes := storeSem_payload_length hsem v
  have hi0lt : i0 < ws.length := by omega
  have haddr_eq : addr = rwBase + BitVec.ofNat 64 i0 := by
    rw [hi0_def]
    bv_omega
  have hover : rwBase.toNat + i0 < 2 ^ 64 := by
    have h1 : rwBase.toNat + ws.length < 2 ^ 64 := hwf.2.1
    omega
  have haddr_toNat : addr.toNat = rwBase.toNat + i0 := by
    rw [haddr_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hvalidmem : isValidMemAddr addr = true := by
    rw [haddr_eq]
    exact hwf.2.2 _ hi0lt
  have hb8 : rwBase.toNat % 8 = 0 := hwf.1
  have halignD : alignToDword addr = rwBase + BitVec.ofNat 64 (8 * (i0 / 8)) := by
    conv_lhs => rw [haddr_eq]
    exact alignToDword_add_ofNat_of_aligned hb8 hover
  have hbo : byteOffset addr = i0 % 8 := by
    conv_lhs => rw [haddr_eq]
    exact byteOffset_add_ofNat_of_aligned hb8 hover
  have hcell : s.getMem (rwBase + BitVec.ofNat 64 (8 * (i0 / 8)))
      = packBytes ((ws.drop (8 * (i0 / 8))).take 8) :=
    holdsFor_bytesRegion_cell hPR2 hi0lt
  -- the one machine step and its effect on the containing cell
  have hkey : (step s = some (execInstrBr s i)
      ∧ execInstrBr s i
        = (s.setMem (rwBase + BitVec.ofNat 64 (8 * (i0 / 8)))
            (packBytes (setBytes ((ws.drop (8 * (i0 / 8))).take 8) (i0 % 8)
              (st.payload v)))).setPC (s.pc + 4))
      ∧ i0 % 8 + st.nbytes ≤ 8 := by
    cases i <;> simp only [storeSem, reduceCtorEq] at hsem
    case SB rs1 rs2 ofs =>
      injection hsem with hsem; subst hsem
      have hmod8 : i0 % 8 + 1 ≤ 8 := by omega
      have hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidByteAccess addr = true
        simpa using hvalidmem
      refine ⟨⟨step_sb hfetch hvalid, ?_⟩, hmod8⟩
      simp only [execInstrBr]
      rw [hrs1v, hrs2v]
      show (s.setByte addr (v.truncate 8)).setPC _ = _
      have hchunklen : i0 % 8 < ((ws.drop (8 * (i0 / 8))).take 8).length := by
        have hin' : i0 + 1 ≤ ws.length := hin
        simp only [List.length_take, List.length_drop]
        have := Nat.div_add_mod i0 8
        omega
      rw [setByte_eq, halignD, hbo, hcell,
        packBytes_set _ (i0 % 8) (v.truncate 8) (by omega) hchunklen]
      rfl
    case SH rs1 rs2 ofs =>
      injection hsem with hsem; subst hsem
      have hdvd' : 2 ∣ i0 := hdvd
      have hin' : i0 + 2 ≤ ws.length := hin
      have hmod8 : i0 % 8 + 2 ≤ 8 := by omega
      have hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidHalfwordAccess addr = true
        simp only [isValidHalfwordAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned2_eq, beq_iff_eq]
        omega
      refine ⟨⟨step_sh hfetch hvalid, ?_⟩, hmod8⟩
      simp only [execInstrBr]
      rw [hrs1v, hrs2v]
      show (s.setHalfword addr (v.truncate 16)).setPC _ = _
      have hchunklen : i0 % 8 + 2 ≤ ((ws.drop (8 * (i0 / 8))).take 8).length := by
        simp only [List.length_take, List.length_drop]
        have := Nat.div_add_mod i0 8
        omega
      rw [setHalfword_eq, halignD, hbo, hcell,
        packBytes_setBytes_halfword _ (i0 % 8) (v.truncate 16)
          (by omega) hmod8 hchunklen]
    case SW rs1 rs2 ofs =>
      injection hsem with hsem; subst hsem
      have hdvd' : 4 ∣ i0 := hdvd
      have hin' : i0 + 4 ≤ ws.length := hin
      have hmod8 : i0 % 8 + 4 ≤ 8 := by omega
      have hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidMemAccess addr = true
        simp only [isValidMemAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned4, beq_iff_eq]
        omega
      refine ⟨⟨step_sw hfetch hvalid, ?_⟩, hmod8⟩
      simp only [execInstrBr]
      rw [hrs1v, hrs2v]
      show (s.setWord32 addr (v.truncate 32)).setPC _ = _
      have hchunklen : i0 % 8 + 4 ≤ ((ws.drop (8 * (i0 / 8))).take 8).length := by
        simp only [List.length_take, List.length_drop]
        have := Nat.div_add_mod i0 8
        omega
      rw [setWord32_eq, halignD, hbo, hcell,
        packBytes_setBytes_word32 _ (i0 % 8) (v.truncate 32)
          (by omega) hmod8 hchunklen]
    case SD rs1 rs2 ofs =>
      injection hsem with hsem; subst hsem
      have hdvd' : 8 ∣ i0 := hdvd
      have hin' : i0 + 8 ≤ ws.length := hin
      have h80 : i0 % 8 = 0 := by omega
      have hi08 : 8 * (i0 / 8) = i0 := by omega
      have hvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 ofs) = true := by
        rw [hrs1v]
        show isValidDwordAccess addr = true
        simp only [isValidDwordAccess_eq, Bool.and_eq_true]
        refine ⟨hvalidmem, ?_⟩
        simp only [isAligned8, beq_iff_eq]
        omega
      refine ⟨⟨step_sd hfetch hvalid, ?_⟩, show i0 % 8 + 8 ≤ 8 from by omega⟩
      simp only [execInstrBr]
      rw [hrs1v, hrs2v]
      show (s.setMem addr v).setPC _ = _
      rw [h80,
        show addr = rwBase + BitVec.ofNat 64 (8 * (i0 / 8)) from by
          rw [haddr_eq, hi08],
        ← packBytes_setBytes_dword ((ws.drop (8 * (i0 / 8))).take 8) v (by
          simp only [List.length_take, List.length_drop]
          omega)]
  obtain ⟨⟨hstep', hexec⟩, hmod8⟩ := hkey
  have hupd := holdsFor_bytesRegion_setBytes
    (i := i0) (ns := st.payload v) hPR2
    (List.ne_nil_of_length_pos (by omega))
    (by omega)
    (by omega)
  refine ⟨1, Nat.le_refl 1,
    (s.setMem (rwBase + BitVec.ofNat 64 (8 * (i0 / 8)))
      (packBytes (setBytes ((ws.drop (8 * (i0 / 8))).take 8) (i0 % 8)
        (st.payload v)))).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · rw [sepConj_left_comm] at hupd
    rw [← sepConj_assoc'] at hupd
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regFileIs _)
        (bytesRegion_pcFree _ _)) hR) hupd

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

/-- Embed a reachable set as an assertion: some symbolic state in the set
    owns the exposed registers, the writable region's contents (whose byte
    count is pinned to the region's length), and the ambient assertion
    component (pinned pc-free). -/
def asrtOf (rw : RwRegion) (reach : Reach) : Assertion :=
  fun h => ∃ rf ws A, ws.length = rw.len ∧ Assertion.pcFree A ∧ reach rf ws A ∧
    (((regFileIs rf) ** bytesRegion rw.base ws) ** A) h

theorem pcFree_asrtOf (rw : RwRegion) (reach : Reach) :
    (asrtOf rw reach).pcFree := by
  intro h hp
  obtain ⟨rf, ws, A, -, hApc, -, hh⟩ := hp
  exact pcFree_sepConj
    (pcFree_sepConj (pcFree_regFileIs _) (bytesRegion_pcFree _ _)) hApc h hh

/-- Leaf-shaped embedding of a reachable set: the exposed register file, the
    writable region's contents, plus the function's read-only region. -/
def asrtM (reg : Region) (rw : RwRegion) (reach : Reach) : Assertion :=
  asrtOf rw reach ** bytesRegion reg.base reg.bytes

theorem pcFree_asrtM (reg : Region) (rw : RwRegion) (reach : Reach) :
    (asrtM reg rw reach).pcFree :=
  pcFree_sepConj (pcFree_asrtOf _ _) (bytesRegion_pcFree _ _)

theorem asrtM_mono {reg : Region} {rw : RwRegion} {r₁ r₂ : Reach}
    (h : ∀ rf ws A, r₁ rf ws A → r₂ rf ws A) :
    ∀ hp, asrtM reg rw r₁ hp → asrtM reg rw r₂ hp :=
  fun hp => sepConj_mono_left (fun hq hh => by
    obtain ⟨rf, ws, A, hlen, hApc, hr, hsts⟩ := hh
    exact ⟨rf, ws, A, hlen, hApc, h rf ws A hr, hsts⟩) hp

theorem asrtM_unsat {reg : Region} {rw : RwRegion} {r : Reach}
    (h : ∀ rf ws A, r rf ws A → False) :
    ∀ hp, asrtM reg rw r hp → False := by
  rintro hp ⟨h1, h2, -, -, ⟨rf, ws, A, -, -, hr, -⟩, -⟩
  exact h rf ws A hr

/-- Split an `asrtM` precondition into a per-symbolic-state family with both
    regions and the (pc-free) ambient assertion alongside. -/
theorem cpsTripleWithin_exists_pre_M {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {reg : Region} {rw : RwRegion} {reach : Reach} {Q : Assertion}
    (h : ∀ rf ws (A : Assertion), ws.length = rw.len → A.pcFree →
      reach rf ws A →
      cpsTripleWithin n entry exit_ cr
        (((regFileIs rf) ** (bytesRegion reg.base reg.bytes **
          bytesRegion rw.base ws)) ** A) Q) :
    cpsTripleWithin n entry exit_ cr (asrtM reg rw reach) Q := by
  intro R hR s hcr hPR hpc
  rw [show asrtM reg rw reach
    = (asrtOf rw reach ** bytesRegion reg.base reg.bytes) from rfl,
    sepConj_assoc'] at hPR
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, ws, A, hlen, hApc, hreach, hsts⟩, hR2⟩ := hPR
  have hPR' : ((((regFileIs rf) ** bytesRegion rw.base ws) ** A) **
      (bytesRegion reg.base reg.bytes ** R)).holdsFor s :=
    ⟨hp, hcompat, h1, h2, hd, hu, hsts, hR2⟩
  rw [sepConj_assoc' ((regFileIs rf) ** bytesRegion rw.base ws) A,
    sepConj_left_comm A (bytesRegion reg.base reg.bytes) R,
    sepConj_assoc' (regFileIs rf) (bytesRegion rw.base ws),
    sepConj_left_comm (bytesRegion rw.base ws) (bytesRegion reg.base reg.bytes),
    ← sepConj_assoc' (bytesRegion reg.base reg.bytes) (bytesRegion rw.base ws),
    ← sepConj_assoc' (regFileIs rf),
    ← sepConj_assoc'
      ((regFileIs rf) ** (bytesRegion reg.base reg.bytes ** bytesRegion rw.base ws))
      A R] at hPR'
  exact h rf ws A hlen hApc hreach R hR s hcr hPR' hpc

end SAsm
end EvmAsm.Rv64
