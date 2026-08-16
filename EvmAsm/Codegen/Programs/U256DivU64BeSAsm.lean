/-
  EvmAsm.Codegen.Programs.U256DivU64BeSAsm

  SAsm model for `u256_div_u64_be`: divide a 32-byte big-endian value by a
  scalar u64 divisor, write the 32-byte quotient, and return the final
  remainder in `a0`.

  The emitted routine is a top-guarded loop whose back-edge re-runs a header
  instruction (`li t2, 32`) before testing the guard.  This file is the first
  consumer of `Stmt.whileHeader`.
-/

import EvmAsm.Codegen.GuestLayout
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.U256Prog
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256DivU64BeSAsm

/-- One byte of big-endian long division, computed exactly as the RV64 code
    does.  The stored quotient byte is the low byte of `DIVU num b`; the next
    remainder is `REMU num b`. -/
def divByteStep (byte : BitVec 8) (b rem : Word) : BitVec 8 × Word :=
  let num : Word := (rem <<< (8 : Nat)) ||| byte.zeroExtend 64
  ((rv64_divu num b).truncate 8, rv64_remu num b)

/-- Pure model of the loop after `k` processed big-endian bytes, walking from
    byte 0 to byte 31.  The state is `(outputBytes, remainder)`. -/
def divState (a orig : List (BitVec 8)) (b : Word) : Nat → List (BitVec 8) × Word
  | 0 => (orig, 0)
  | k + 1 =>
      let st := divState a orig b k
      let step := divByteStep (a.getD k 0) b st.2
      (st.1.set k step.1, step.2)

private theorem divState_succ (a orig : List (BitVec 8)) (b : Word) (k : Nat) :
    divState a orig b (k + 1) =
      let st := divState a orig b k
      let step := divByteStep (a.getD k 0) b st.2
      (st.1.set k step.1, step.2) := by
  rfl

/-- Final 32-byte big-endian quotient bytes. -/
def u256DivU64BeQuotBytes (a orig : List (BitVec 8)) (b : Word) : List (BitVec 8) :=
  (divState a orig b 32).1

/-- Final u64 remainder returned in `a0`. -/
def u256DivU64BeRemainder (a orig : List (BitVec 8)) (b : Word) : Word :=
  (divState a orig b 32).2

/-- Focus relation for the read-only input at `a0`. -/
def roSrc (srcPtr : Word) (srcBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x10 = srcPtr ∧ rob = srcBytes ∧ rest = empAssertion

/-- Loop invariant at the header-reloaded guard point. -/
def u256DivU64BeInv (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws A =>
    rf.get .x10 = srcPtr ∧
    rf.get .x11 = b ∧
    rf.get .x12 = outPtr ∧
    rf.get .x5 = (divState srcBytes orig b k).2 ∧
    rf.get .x6 = BitVec.ofNat 64 k ∧
    rf.get .x7 = (32 : Word) ∧
    ws = (divState srcBytes orig b k).1 ∧
    k ≤ 32 ∧
    0 < b.toNat ∧ b.toNat ≤ 2 ^ 56 ∧
    srcBytes.length = 32 ∧ orig.length = 32 ∧
    srcPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
    (srcPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ srcPtr.toNat) ∧
    A = bytesRegion srcPtr srcBytes

/-- Loop post before the final `mv a0, rem`: all bytes processed. -/
def u256DivU64BeLoopPost (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = srcPtr ∧ rf.get .x11 = b ∧ rf.get .x12 = outPtr ∧
    rf.get .x5 = u256DivU64BeRemainder srcBytes orig b ∧
    rf.get .x6 = (32 : Word) ∧ rf.get .x7 = (32 : Word) ∧
    ws = u256DivU64BeQuotBytes srcBytes orig b ∧
    A = bytesRegion srcPtr srcBytes

/-- Function precondition: one read-only 32-byte input and one writable output
    window.  Disjointness is the routing fact required by the current SAsm
    read/write ownership model. -/
def u256DivU64BePre (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = srcPtr ∧ rf.get .x11 = b ∧ rf.get .x12 = outPtr ∧
    ws = orig ∧
    0 < b.toNat ∧ b.toNat ≤ 2 ^ 56 ∧
    srcBytes.length = 32 ∧ orig.length = 32 ∧
    srcPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
    (srcPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ srcPtr.toNat) ∧
    A = bytesRegion srcPtr srcBytes

/-- Function postcondition: `a0` is the final remainder and the output window is
    the byte-by-byte long-division quotient. -/
def u256DivU64BePost (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = u256DivU64BeRemainder srcBytes orig b ∧
    rf.get .x11 = b ∧ rf.get .x12 = outPtr ∧
    ws = u256DivU64BeQuotBytes srcBytes orig b ∧
    A = bytesRegion srcPtr srcBytes

/-- Byte-identical loop body between the top guard and the back-edge. -/
def u256DivU64BeLoopBody (srcPtr _outPtr : Word)
    (srcBytes _orig : List (BitVec 8)) : Stmt :=
  .block "addrRead" [.ADD .x28 .x10 .x6] ;;;
  .readAt "readA" .x10 (roSrc srcPtr srcBytes) [.LBU .x29 .x28 (0 : BitVec 12)] ;;;
  .block "divStore"
    [.SLLI .x30 .x5 (8 : BitVec 6),
     .OR .x30 .x30 .x29,
     .DIVU .x31 .x30 .x11,
     .REMU .x5 .x30 .x11,
     .ADD .x28 .x12 .x6,
     .SB .x28 .x31 (0 : BitVec 12),
     .ADDI .x6 .x6 (1 : BitVec 12)]

/-- Byte-identical structured body, excluding the final `ret` epilogue handled
    by `Fn.Spec`. -/
def u256DivU64BeBody (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word), .LI .x6 (0 : Word)] ;;;
  .whileHeader "loop"
    (.block "header" [.LI .x7 (32 : Word)])
    (.bne .x6 .x7)
    32
    (u256DivU64BeInv srcPtr outPtr b srcBytes orig)
    (u256DivU64BeLoopBody srcPtr outPtr srcBytes orig) ;;;
  .block "retVal" [.MV .x10 .x5]

def u256DivU64BeFn (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) : Fn where
  name := "u256DivU64Be"
  region := Region.empty
  rw := ⟨outPtr, 32⟩
  pre := u256DivU64BePre srcPtr outPtr b srcBytes orig
  post := u256DivU64BePost srcPtr outPtr b srcBytes orig
  body := u256DivU64BeBody srcPtr outPtr b srcBytes orig

/-- Layout-independence interlock: the body flattens to `u256DivU64Be_prog_of
    L` for an ARBITRARY layout `L`, so the body cannot reference the layout.
    (`rfl` closes it; a future layout reference would make it fail.) -/
theorem u256DivU64BeBody_flatten (L : GuestLayout) :
    (u256DivU64BeBody 0 0 1 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
      = u256DivU64Be_prog_of L := rfl

#guard (u256DivU64BeBody 0 0 1 [] []).flatten 0 =
  (u256DivU64BeBody 0 0 1 [] []).flatten 0x80000000


/-! ## Local proof helpers -/

private theorem nat_lt_32_toNat (i : Nat) (hi : i < 32) :
    (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat]
  omega

private theorem add_idx_sub_self (ptr : Word) (i : Nat) (hi : i < 32) :
    (ptr + BitVec.ofNat 64 i - ptr).toNat = i := by
  have hidx : (BitVec.ofNat 64 i).toNat = i := nat_lt_32_toNat i hi
  rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]
  omega

private theorem add_idx_sub_base (ptr base : Word) (i : Nat) (hi : i < 32) :
    (ptr + BitVec.ofNat 64 i - base).toNat =
      (ptr.toNat + i + (2 ^ 64 - base.toNat)) % 2 ^ 64 := by
  have hidx : (BitVec.ofNat 64 i).toNat = i := nat_lt_32_toNat i hi
  rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]
  omega

private theorem not_inRw_disjoint32 (ptr outPtr : Word) (ws : List (BitVec 8))
    (i : Nat) (hi : i < 32)
    (hws : ws.length = 32)
    (hptr : ptr.toNat + 32 < 2 ^ 64)
    (hout : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : ptr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ ptr.toNat) :
    ¬ inRw outPtr ws (ptr + BitVec.ofNat 64 i) 1 := by
  unfold inRw
  rw [hws, add_idx_sub_base ptr outPtr i hi]
  intro hcontra
  rcases hdisj with hd | hd <;> omega

private theorem byteAt_idx (ptr : Word) (bytes : List (BitVec 8)) (i : Nat) (hi : i < 32) :
    Region.byteAt ⟨ptr, bytes⟩ (ptr + BitVec.ofNat 64 i) = bytes.getD i 0 := by
  unfold Region.byteAt
  rw [add_idx_sub_self ptr i hi]

private theorem readLbu_blockVCs (ptr outPtr : Word) (rf : RegFile) (ws robytes : List (BitVec 8))
    (rd addrReg : Reg) (i : Nat) (hi : i < 32)
    (haddr : rf.get addrReg = ptr + BitVec.ofNat 64 i)
    (hws : ws.length = 32)
    (hroLen : robytes.length = 32)
    (hptrBound : ptr.toNat + 32 < 2 ^ 64)
    (houtBound : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : ptr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ ptr.toNat) :
    blockVCs ⟨ptr, robytes⟩ outPtr rf ws [.LBU rd addrReg (0 : BitVec 12)] := by
  have haddr0 : rf.get addrReg + signExtend12 (0 : BitVec 12)
      = ptr + BitVec.ofNat 64 i := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  refine ⟨?_, trivial⟩
  show (if inRw outPtr ws (rf.get addrReg + signExtend12 (0 : BitVec 12)) 1
    then _ else Region.loadOk _ _ _)
  rw [haddr0, if_neg (not_inRw_disjoint32 ptr outPtr ws i hi hws hptrBound houtBound hdisj)]
  unfold Region.loadOk
  change 1 ∣ (ptr + BitVec.ofNat 64 i - ptr).toNat ∧
    (ptr + BitVec.ofNat 64 i - ptr).toNat + 1 ≤ robytes.length
  rw [add_idx_sub_self ptr i hi, hroLen]
  exact ⟨one_dvd _, by omega⟩

private theorem execBlock_lbu_ws (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs : Reg) (ofs : BitVec 12) :
    (execBlock ro rwBase rf ws [.LBU rd rs ofs]).2 = ws := by
  rw [execBlock_cons, execBlock_nil, execInstrRF]
  dsimp only [aluSem, loadSem]

private theorem execBlock_lbu_get_ne (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs : Reg) (ofs : BitVec 12) (r : Reg)
    (hne : r ≠ rd) :
    (execBlock ro rwBase rf ws [.LBU rd rs ofs]).1.get r = rf.get r := by
  rw [execBlock_cons, execBlock_nil, execInstrRF]
  dsimp only [aluSem, loadSem]
  by_cases h : inRw rwBase ws (rf.get rs + signExtend12 ofs) 1
  · rw [if_pos h, RegFile.get_set_ne _ _ _ _ hne]
  · rw [if_neg h, RegFile.get_set_ne _ _ _ _ hne]

private theorem execBlock_lbu_ro_idx (ptr outPtr : Word) (rf : RegFile)
    (ws robytes : List (BitVec 8)) (rd addrReg : Reg) (i : Nat) (hi : i < 32)
    (haddr : rf.get addrReg = ptr + BitVec.ofNat 64 i)
    (hws : ws.length = 32)
    (hptrBound : ptr.toNat + 32 < 2 ^ 64)
    (houtBound : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : ptr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ ptr.toNat) :
    execBlock ⟨ptr, robytes⟩ outPtr rf ws [.LBU rd addrReg (0 : BitVec 12)] =
      (rf.set rd ((robytes.getD i 0).zeroExtend 64), ws) := by
  have haddr0 : rf.get addrReg + signExtend12 (0 : BitVec 12)
      = ptr + BitVec.ofNat 64 i := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  rw [execBlock_cons, execInstrRF]
  dsimp only [aluSem, loadSem]
  rw [if_neg (by
    rw [haddr0]
    exact not_inRw_disjoint32 ptr outPtr ws i hi hws hptrBound houtBound hdisj)]
  rw [haddr0, byteAt_idx ptr robytes i hi, execBlock_nil]

private theorem divStore_effect (outPtr : Word) (rf : RegFile) (ws : List (BitVec 8))
    (i : Nat) (hi : i < 32) (byte : BitVec 8) (b rem : Word)
    (hx29 : rf.get .x29 = byte.zeroExtend 64)
    (hx5 : rf.get .x5 = rem)
    (hx6 : rf.get .x6 = BitVec.ofNat 64 i)
    (hx11 : rf.get .x11 = b)
    (hx12 : rf.get .x12 = outPtr) :
    let r := execBlock Region.empty outPtr rf ws
      [.SLLI .x30 .x5 (8 : BitVec 6),
       .OR .x30 .x30 .x29,
       .DIVU .x31 .x30 .x11,
       .REMU .x5 .x30 .x11,
       .ADD .x28 .x12 .x6,
       .SB .x28 .x31 (0 : BitVec 12),
       .ADDI .x6 .x6 (1 : BitVec 12)]
    r.1.get .x10 = rf.get .x10 ∧
    r.1.get .x11 = b ∧
    r.1.get .x12 = outPtr ∧
    r.1.get .x5 = (divByteStep byte b rem).2 ∧
    r.1.get .x6 = BitVec.ofNat 64 (i + 1) ∧
    r.2 = ws.set i (divByteStep byte b rem).1 := by
  dsimp only
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ (0 : BitVec 12) i (by
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
    rw [hx12, hx6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    rw [show outPtr + BitVec.ofNat 64 i + (0 : Word) = outPtr + BitVec.ofNat 64 i by bv_omega]
    exact add_idx_sub_self outPtr i hi)]
  rw [execBlock_cons, execBlock_nil]
  dsimp only [execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]
  unfold divByteStep
  simp only [hx29, hx5, hx11, hx12]
  refine ⟨trivial, trivial, trivial, rfl, ?_, ?_⟩
  · rw [hx6, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    bv_omega
  · rw [show (8 : BitVec 6).toNat = 8 from rfl]
    rw [show setBytes ws i [(rv64_divu ((rem <<< 8) ||| BitVec.zeroExtend 64 byte) b).truncate 8]
        = ws.set i ((rv64_divu ((rem <<< 8) ||| BitVec.zeroExtend 64 byte) b).truncate 8) from rfl]


private theorem u256DivU64BeLoopBody_effect (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨outPtr, 32⟩ (u256DivU64BeLoopBody srcPtr outPtr srcBytes orig)
        (fun rf ws A =>
          u256DivU64BeInv srcPtr outPtr b srcBytes orig i rf ws A ∧
          Cond.holds (.bne .x6 .x7) rf) rf' ws' A' →
      rf'.get .x10 = srcPtr ∧
      rf'.get .x11 = b ∧
      rf'.get .x12 = outPtr ∧
      rf'.get .x5 = (divState srcBytes orig b (i + 1)).2 ∧
      rf'.get .x6 = BitVec.ofNat 64 (i + 1) ∧
      ws' = (divState srcBytes orig b (i + 1)).1 ∧
      i < 32 ∧
      0 < b.toNat ∧ b.toNat ≤ 2 ^ 56 ∧
      srcBytes.length = 32 ∧ orig.length = 32 ∧
      srcPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
      (srcPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ srcPtr.toNat) ∧
      A' = bytesRegion srcPtr srcBytes := by
  intro rf' ws' A' hsp
  unfold u256DivU64BeLoopBody at hsp
  obtain ⟨rfS, wsS, hwsS, hreachA, hrf', hws'⟩ := hsp
  obtain ⟨rfA0, wsA0, AA, robA, restA, hlenARead, hreach0, _hsatA,
    hroArel, hrfA, hwsA, hAeqA⟩ := hreachA
  obtain ⟨rf0, ws0, hws0, ⟨hinv, _hguard⟩, hrf0, hws0eq⟩ := hreach0
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hiLe, hbPos, hbBound,
    hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
  obtain ⟨hptrA, hrobA, hrestA⟩ := hroArel
  dsimp only [u256DivU64BeFn] at hlenARead hrf0 hws0eq hrfA hwsA hrf' hws'
  have hiLt : i < 32 := by
    simp only [Cond.holds] at _hguard
    by_contra hnot
    have hi32 : i = 32 := by omega
    subst hi32
    rw [hx6, hx7] at _hguard
    exact _hguard rfl
  have haddrA : rfA0.get .x28 = rfA0.get .x10 + BitVec.ofNat 64 i := by
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx6]
  have hreadA : execBlock { base := rfA0.get .x10, bytes := robA } outPtr rfA0 wsA0
      [.LBU .x29 .x28 (0 : BitVec 12)] =
      (rfA0.set .x29 ((srcBytes.getD i 0).zeroExtend 64), wsA0) := by
    rw [hrobA]
    apply execBlock_lbu_ro_idx
    · exact hiLt
    · exact haddrA
    · exact hlenARead
    · rw [hptrA]
      exact hplA
    · exact hplO
    · rw [hptrA]
      exact hdisjA
  have hwsSeq : wsS = (divState srcBytes orig b i).1 := by
    rw [hwsA, execBlock_lbu_ws, hws0eq]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    exact hwsState
  have hx29S : rfS.get .x29 = (srcBytes.getD i 0).zeroExtend 64 := by
    rw [hrfA, hreadA, RegFile.get_set_self _ _ _ (by decide)]
  have hx5S : rfS.get .x5 = (divState srcBytes orig b i).2 := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx5
  have hx6S : rfS.get .x6 = BitVec.ofNat 64 i := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx6
  have hx11S : rfS.get .x11 = b := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hx12S : rfS.get .x12 = outPtr := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12
  have hdiv := divStore_effect outPtr rfS wsS i hiLt (srcBytes.getD i 0) b
    (divState srcBytes orig b i).2 hx29S hx5S hx6S hx11S hx12S
  dsimp only at hdiv
  obtain ⟨hsx10, hsx11, hsx12, hsx5, hsx6, hsws⟩ := hdiv
  have hAfinal : A' = bytesRegion srcPtr srcBytes := by
    rw [hAeqA, hptrA, hrobA, hrestA]
    exact sepConj_emp_right' _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hiLt, hbPos, hbBound, hlenA, hlenO,
    hplA, hplO, hdisjA, hAfinal⟩
  · rw [hrf', hsx10]
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrf', hsx11]
  · rw [hrf', hsx12]
  · rw [hrf', hsx5]
    rw [divState_succ]
  · rw [hrf', hsx6]
  · rw [hws', hsws, hwsSeq]
    rw [divState_succ]

private theorem divStore_blockVCs (outPtr : Word) (rf : RegFile) (ws : List (BitVec 8))
    (i : Nat) (hi : i < 32)
    (hx6 : rf.get .x6 = BitVec.ofNat 64 i)
    (hx12 : rf.get .x12 = outPtr)
    (hws : ws.length = 32) :
    blockVCs Region.empty outPtr rf ws
      [.SLLI .x30 .x5 (8 : BitVec 6),
       .OR .x30 .x30 .x29,
       .DIVU .x31 .x30 .x11,
       .REMU .x5 .x30 .x11,
       .ADD .x28 .x12 .x6,
       .SB .x28 .x31 (0 : BitVec 12),
       .ADDI .x6 .x6 (1 : BitVec 12)] := by
  simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true, inRw]
  rw [hx12, hx6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  rw [show outPtr + BitVec.ofNat 64 i + (0 : Word) = outPtr + BitVec.ofNat 64 i by bv_omega]
  rw [add_idx_sub_self outPtr i hi, hws]
  simp only [one_dvd, and_true, true_and]
  omega

/-! ## Post bridge -/

/-- Final post bridge for `u256_div_u64_be`: after the loop has produced the
    final remainder in `x5`, the trailing `mv a0, t0` establishes the function
    post. -/
theorem u256DivU64Be_retVal_post (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) :
    ∀ rf ws A,
      sp Region.empty ⟨outPtr, 32⟩ (.block "retVal" [.MV .x10 .x5])
        (u256DivU64BeLoopPost srcPtr outPtr b srcBytes orig) rf ws A →
      u256DivU64BePost srcPtr outPtr b srcBytes orig rf ws A := by
  rintro rf ws A ⟨rf₀, ws₀, hws₀, hloop, hrf, hws⟩
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsBytes, hA⟩ := hloop
  subst hrf
  subst hws
  unfold u256DivU64BePost
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [RegFile.get_set_self _ _ _ (by decide), hx5]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]
  · exact hwsBytes
  · exact hA


theorem u256DivU64Be_spec (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (base : Word) :
    (u256DivU64BeFn srcPtr outPtr b srcBytes orig).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case u256DivU64Be.loop.inv_init =>
    rintro rf ws A ⟨rfH, wsH, hwsH, hinit, hrf, hws⟩
    obtain ⟨rf₀, ws₀, hws₀, hpre, hrfH, hwsH_eq⟩ := hinit
    obtain ⟨hx10, hx11, hx12, hwsOrig, hbPos, hbBound, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩ := hpre
    dsimp only [u256DivU64BeFn] at hws₀ hwsH hrfH hwsH_eq hrf hws
    subst hrf
    subst hws
    subst hrfH
    subst hwsH_eq
    unfold u256DivU64BeInv
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hbPos, hbBound, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · exact hwsOrig
  case u256DivU64Be.loop.inv_step =>
    rintro i hiLt rf' ws' A' hsp
    obtain ⟨rfB, wsB, hwsB, hbody, hrf', hws'⟩ := hsp
    have hb := u256DivU64BeLoopBody_effect srcPtr outPtr b srcBytes orig i rfB wsB A' hbody
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hbPos, hbBound, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩ := hb
    subst hrf'
    subst hws'
    unfold u256DivU64BeInv
    simp only [u256DivU64BeFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hbPos, hbBound, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), hx5]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7), hx6]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · exact hwsState
  case u256DivU64Be.loop.exhausted =>
    rintro rf ws A hinv
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hiLe, hbPos, hbBound,
      hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
    simp only [Cond.holds]
    rw [hx6, hx7]
    intro h_ne
    exact h_ne rfl
  case u256DivU64Be.loop.body.readA.focus =>
    rintro rf ws A hreach hApc hp hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hguard⟩, hrf, hws⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos, hbBound,
      hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
    dsimp only [u256DivU64BeFn] at hrf hws hws₀
    subst hrf
    subst hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true] at hhp ⊢
    have hx10' : rf₀.get .x10 = srcPtr := hx10
    refine ⟨srcBytes, empAssertion, ⟨?_, rfl, rfl⟩, ?_, pcFree_emp, ?_⟩
    · exact hx10'
    · rw [hA] at hhp
      rw [hx10', sepConj_emp_right']
      exact hhp
    · rw [hx10']
      exact hroSrc
  case u256DivU64Be.loop.body.readA.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hguard⟩, hrf, hwsEq⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos, hbBound,
      hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    dsimp only [u256DivU64BeFn] at hrf hws hws₀ hwsEq ⊢
    have hws32 : ws.length = 32 := hws
    subst hrf
    subst hwsEq
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true] at hptr hrob hrest ⊢
    have haddr : (rf₀.set Reg.x28 (rf₀.get Reg.x10 + rf₀.get Reg.x6)).get Reg.x28 =
        rf₀.get Reg.x10 + BitVec.ofNat 64 i := by
      rw [RegFile.get_set_self _ _ _ (by decide), hx6]
    exact readLbu_blockVCs (rf₀.get .x10) outPtr _ ws robytes .x29 .x28 i hi haddr hws32
      (by rw [hrob]; exact hlenA) (by rw [hptr]; exact hplA) hplO
      (by rw [hptr]; exact hdisjA)
  case u256DivU64Be.loop.body.divStore.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rfA, wsA, AA, robA, restA, hlenARead, hreach0, hsatA,
      hroArel, hrfA, hwsA, hAeqA⟩ := hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hguard⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos, hbBound,
      hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
    dsimp only [u256DivU64BeFn] at hrfA hrf0 hwsA hws0 hlenARead hws₀ hws ⊢
    have hws32 : ws.length = 32 := hws
    have hx6' : rf.get .x6 = BitVec.ofNat 64 i := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x29 .x28 (0 : BitVec 12) .x6 (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx6]
    have hx12' : rf.get .x12 = outPtr := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x29 .x28 (0 : BitVec 12) .x12 (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx12]
    exact divStore_blockVCs outPtr rf ws i hi hx6' hx12' hws32
  case u256DivU64Be.post =>
    intro rf ws A h
    unfold u256DivU64BeFn u256DivU64BeBody at h
    obtain ⟨rfLoop, wsLoop, hwsLoop, hloopExit, hrf, hws⟩ := h
    obtain ⟨⟨i, hiFuel, hinv⟩, hnotGuard⟩ := hloopExit
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos, hbBound,
      hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
    have heq : rfLoop.get .x6 = rfLoop.get .x7 := by
      by_contra h_ne
      exact hnotGuard h_ne
    have hiEq : i = 32 := by
      have hto := congrArg BitVec.toNat heq
      have hiToNat : (BitVec.ofNat 64 i).toNat = i := by
        rw [BitVec.toNat_ofNat]
        omega
      rw [hx6, hx7, hiToNat, show ((32 : Word).toNat = 32) from by decide] at hto
      omega
    subst hiEq
    subst hrf
    subst hws
    unfold u256DivU64BePost u256DivU64BeRemainder u256DivU64BeQuotBytes
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]
    · exact hwsState
    · exact hA


/-! ## Flat linked-entry contract

    The structured `Fn.Spec` above is ambient-aware because the 32-byte source
    is read-only.  This adapter anchors that contract at the deployed entry,
    preserving the source region in the ambient assertion and exposing the
    quotient window plus the ABI registers at the call boundary.
-/

def u256DivU64BeCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.u256_div_u64_be : Word) u256DivU64Be_prog

def u256DivU64BeScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_u256Div (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf u256DivU64BeScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [u256DivU64BeScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem u256Div_args_notin_scratch :
    ∀ r ∈ u256DivU64BeScratch,
      r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) := by
  decide

theorem u256DivU64BeFlat_spec (ret srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroSrc : Region.wf ⟨srcPtr, srcBytes⟩)
    (hlenSrc : srcBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovSrc : srcPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : srcPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ srcPtr.toNat)
    (hbPos : 0 < b.toNat)
    (hbBound : b.toNat ≤ 2 ^ 56)
    (hsz : 4 * ((u256DivU64BeFn srcPtr outPtr b srcBytes orig).body.size + 1)
      ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((u256DivU64BeFn srcPtr outPtr b srcBytes orig).body.steps + 1)
      (GuestAddrs.u256_div_u64_be : Word) ret u256DivU64BeCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srcPtr) ** (.x11 ↦ᵣ b) **
        (.x12 ↦ᵣ outPtr) ** regOwns u256DivU64BeScratch **
        bytesRegion outPtr orig ** bytesRegion srcPtr srcBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        (.x10 ↦ᵣ u256DivU64BeRemainder srcBytes orig b) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256DivU64BeScratch **
        bytesRegion outPtr (u256DivU64BeQuotBytes srcBytes orig b) **
        bytesRegion srcPtr srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns u256DivU64BeScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srcPtr) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) ** bytesRegion outPtr orig **
        bytesRegion srcPtr srcBytes)
      (fun vf => ?_))
  have hpre : u256DivU64BePre srcPtr outPtr b srcBytes orig
      (fun r => if r = .x10 then srcPtr else
        if r = .x11 then b else if r = .x12 then outPtr else vf r)
      orig (bytesRegion srcPtr srcBytes) := by
    refine ⟨?_, ?_, ?_, rfl, hbPos, hbBound, hlenSrc, hlenOrig,
      hovSrc, hovOut, hdisj, rfl⟩
    · show RegFile.get _ .x10 = srcPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = b
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = outPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (u256DivU64BeFn srcPtr outPtr b srcBytes orig)
    (GuestAddrs.u256_div_u64_be : Word)
    (u256DivU64Be_spec srcPtr outPtr b srcBytes orig hrw hroSrc
      (GuestAddrs.u256_div_u64_be : Word))
    hsz
    ret halign
    (fun r => if r = .x10 then srcPtr else
      if r = .x11 then b else if r = .x12 then outPtr else vf r)
    orig (bytesRegion srcPtr srcBytes)
    (bytesRegion_pcFree srcPtr srcBytes)
    (by exact hlenOrig) hpre
    (Q := (((.x10 ↦ᵣ u256DivU64BeRemainder srcBytes orig b) **
          (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256DivU64BeScratch) **
        bytesRegion outPtr (u256DivU64BeQuotBytes srcBytes orig b)) **
      bytesRegion srcPtr srcBytes)
    (fun _ _ _ hpost => hpost.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hx10', hx11', hx12', hws', _hA⟩ := hpost
      subst ws'
      have g10 : rf' .x10 = u256DivU64BeRemainder srcBytes orig b := by
        rw [← hx10', RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have g11 : rf' .x11 = b := by
        rw [← hx11', RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      have g12 : rf' .x12 = outPtr := by
        rw [← hx12', RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_u256Div, g10, g11, g12] at hh
      refine sepConj_mono_left (sepConj_mono_left ?_) hp hh
      exact fun h hx => by
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hx
        exact regAtomsOf_to_regOwns (fun r => rf' r) u256DivU64BeScratch)
  rw [show (u256DivU64BeFn srcPtr outPtr b srcBytes orig).programRet
      (GuestAddrs.u256_div_u64_be : Word) = u256DivU64Be_prog from rfl] at had
  rw [show (u256DivU64BeFn srcPtr outPtr b srcBytes orig).region =
      Region.empty from rfl,
    show (u256DivU64BeFn srcPtr outPtr b srcBytes orig).rw.base = outPtr
      from rfl,
    show Region.empty.base = (0 : Word) from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_u256Div,
    show (if (Reg.x10 : Reg) = .x10 then srcPtr else _) = srcPtr
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then srcPtr else
      if (Reg.x11 : Reg) = .x11 then b else _) = b from by
      rw [if_neg (by decide), if_pos rfl],
    show (if (Reg.x12 : Reg) = .x10 then srcPtr else
      if (Reg.x12 : Reg) = .x11 then b else
      if (Reg.x12 : Reg) = .x12 then outPtr else _) = outPtr from by
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl],
    regAtomsOf_congr
      (fun r => if r = .x10 then srcPtr else
        if r = .x11 then b else if r = .x12 then outPtr else vf r)
      vf u256DivU64BeScratch
      (fun r hr => by
        obtain ⟨h10, h11, h12⟩ := u256Div_args_notin_scratch r hr
        show (if r = .x10 then srcPtr else
          if r = .x11 then b else if r = .x12 then outPtr else vf r) = vf r
        rw [if_neg h10, if_neg h11, if_neg h12])] at had
  simp only [sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

/-! ## Alias-safe in-place contract (`srcPtr = outPtr`)

The linked K73 routine invokes this helper with the same pointer in `a0` and
`a2`.  The emitted loop is safe for that exact alias: it loads byte `i`,
computes the quotient byte, stores byte `i`, and only then advances to `i+1`.
The exact-alias case is not a general overlap theorem.  With a partial overlap,
a store at output offset `i` can overwrite a later source byte `j > i` before
that byte is read.  Thus the safe caller premise is the three-way disjunction
`srcPtr = outPtr`, `srcPtr + 32 ≤ outPtr`, or `outPtr + 32 ≤ srcPtr`; the latter
two cases are the disjoint-buffer premise of `u256DivU64BeFlat_spec` above.
This section supplies the second theorem for the live exact-alias call shape,
while the original theorem remains available for the two disjoint shapes. -/

private theorem getD_set_ne_in_place {l : List (BitVec 8)} {i j : Nat}
    {b d : BitVec 8} (h : i ≠ j) :
    (l.set i b).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

private theorem divState_length_in_place
    (a orig : List (BitVec 8)) (b : Word) (k : Nat) :
    (divState a orig b k).1.length = orig.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [divState_succ]
      simp only [List.length_set, ih]

private theorem divState_unprocessed_in_place
    (a : List (BitVec 8)) (b : Word) (k j : Nat)
    (hj : k ≤ j) (hji : j < 32) :
    (divState a a b k).1.getD j 0 = a.getD j 0 := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
      rw [divState_succ]
      rw [getD_set_ne_in_place (by omega : k ≠ j)]
      exact ih j (by omega) hji

def u256DivU64BeInPlaceInv (ptr b : Word)
    (aBytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    rf.get .x5 = (divState aBytes aBytes b k).2 ∧
    rf.get .x6 = BitVec.ofNat 64 k ∧ rf.get .x7 = (32 : Word) ∧
    ws = (divState aBytes aBytes b k).1 ∧ k ≤ 32 ∧
    0 < b.toNat ∧ b.toNat ≤ 2 ^ 56 ∧ aBytes.length = 32 ∧
    ptr.toNat + 32 < 2 ^ 64 ∧ A = empAssertion

def u256DivU64BeInPlaceLoopPost (ptr b : Word)
    (aBytes : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    rf.get .x5 = u256DivU64BeRemainder aBytes aBytes b ∧
    rf.get .x6 = (32 : Word) ∧ rf.get .x7 = (32 : Word) ∧
    ws = u256DivU64BeQuotBytes aBytes aBytes b ∧ A = empAssertion

def u256DivU64BeInPlaceLoopBody (_ptr _b : Word)
    (_aBytes : List (BitVec 8)) : Stmt :=
  .block "addrRead" [.ADD .x28 .x10 .x6] ;;;
  .block "readA" [.LBU .x29 .x28 (0 : BitVec 12)] ;;;
  .block "divStore"
    [.SLLI .x30 .x5 (8 : BitVec 6),
     .OR .x30 .x30 .x29,
     .DIVU .x31 .x30 .x11,
     .REMU .x5 .x30 .x11,
     .ADD .x28 .x12 .x6,
     .SB .x28 .x31 (0 : BitVec 12),
     .ADDI .x6 .x6 (1 : BitVec 12)]

def u256DivU64BeInPlaceBody (ptr b : Word)
    (aBytes : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word), .LI .x6 (0 : Word)] ;;;
  .whileHeader "loop"
    (.block "header" [.LI .x7 (32 : Word)])
    (.bne .x6 .x7)
    32
    (u256DivU64BeInPlaceInv ptr b aBytes)
    (u256DivU64BeInPlaceLoopBody ptr b aBytes) ;;;
  .block "retVal" [.MV .x10 .x5]

def u256DivU64BeInPlaceFn (ptr b : Word)
    (aBytes : List (BitVec 8)) : Fn where
  name := "u256DivU64BeInPlace"
  region := Region.empty
  rw := ⟨ptr, 32⟩
  pre := fun rf ws A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    ws = aBytes ∧ 0 < b.toNat ∧ b.toNat ≤ 2 ^ 56 ∧
    aBytes.length = 32 ∧ ptr.toNat + 32 < 2 ^ 64 ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = u256DivU64BeRemainder aBytes aBytes b ∧
    rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    ws = u256DivU64BeQuotBytes aBytes aBytes b ∧ A = empAssertion
  body := u256DivU64BeInPlaceBody ptr b aBytes

theorem u256DivU64BeInPlaceBody_flatten (L : GuestLayout) :
    (u256DivU64BeInPlaceBody 0 1 []).flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] = u256DivU64Be_prog_of L := by
  rfl

private theorem execBlock_lbu_rw_div (ptr : Word) (rf : RegFile)
    (ws aBytes : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (haddr : rf.get .x28 = ptr + BitVec.ofNat 64 i)
    (hws : ws = (divState aBytes aBytes (rf.get .x11) i).1)
    (hlen : aBytes.length = 32) :
    execBlock Region.empty ptr rf ws
      [.LBU .x29 .x28 (0 : BitVec 12)] =
      (rf.set .x29 ((aBytes.getD i 0).zeroExtend 64), ws) := by
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ i
    (by
      rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega)
    (by
      rw [hws, divState_length_in_place, hlen]
      omega), execBlock_nil]
  rw [hws, divState_unprocessed_in_place aBytes (rf.get .x11) i i
    (by omega) hi]

private theorem readLbuRwDiv_blockVCs (ptr : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (haddr : rf.get .x28 = ptr + BitVec.ofNat 64 i)
    (hws : ws.length = 32) :
    blockVCs Region.empty ptr rf ws
      [.LBU .x29 .x28 (0 : BitVec 12)] := by
  have haddr0 : rf.get .x28 + signExtend12 (0 : BitVec 12) =
      ptr + BitVec.ofNat 64 i := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  refine ⟨?_, trivial⟩
  show (if inRw ptr ws (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1
    then _ else Region.empty.loadOk _ _)
  rw [haddr0, if_pos]
  · unfold Region.loadOk
    change 1 ∣ (ptr + BitVec.ofNat 64 i - ptr).toNat ∧
      (ptr + BitVec.ofNat 64 i - ptr).toNat + 1 ≤ ws.length
    rw [add_idx_sub_self ptr i hi, hws]
    exact ⟨one_dvd _, by omega⟩
  · unfold inRw
    rw [add_idx_sub_self ptr i hi, hws]
    omega

private theorem u256DivU64BeInPlaceLoopBody_effect (ptr b : Word)
    (aBytes : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨ptr, 32⟩
        (u256DivU64BeInPlaceLoopBody ptr b aBytes)
        (fun rf ws A =>
          u256DivU64BeInPlaceInv ptr b aBytes i rf ws A ∧
          Cond.holds (.bne .x6 .x7) rf) rf' ws' A' →
      rf'.get .x10 = ptr ∧
      rf'.get .x11 = b ∧
      rf'.get .x12 = ptr ∧
      rf'.get .x5 = (divState aBytes aBytes b (i + 1)).2 ∧
      rf'.get .x6 = BitVec.ofNat 64 (i + 1) ∧
      ws' = (divState aBytes aBytes b (i + 1)).1 ∧
      i < 32 ∧
      0 < b.toNat ∧ b.toNat ≤ 2 ^ 56 ∧
      aBytes.length = 32 ∧ ptr.toNat + 32 < 2 ^ 64 ∧
      A' = empAssertion := by
  intro rf' ws' A' hsp
  unfold u256DivU64BeInPlaceLoopBody at hsp
  obtain ⟨rfS, wsS, hwsS, hreachRead, hrf', hws'⟩ := hsp
  obtain ⟨rfA0, wsA0, hwsA0, hreachAddr, hrfA, hwsA⟩ := hreachRead
  obtain ⟨rf0, ws0, hws0, ⟨hinv, _hguard⟩, hrf0, hws0eq⟩ := hreachAddr
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hiLe, hbPos,
    hbBound, hlenA, hpl, hA⟩ := hinv
  dsimp only [u256DivU64BeInPlaceFn] at hrf0 hws0eq hrfA hwsA hrf' hws'
  have hiLt : i < 32 := by
    simp only [Cond.holds] at _hguard
    by_contra hnot
    have hi32 : i = 32 := by omega
    subst hi32
    rw [hx6, hx7] at _hguard
    exact _hguard rfl
  have haddrA : rfA0.get .x28 = ptr + BitVec.ofNat 64 i := by
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
    rw [hx10, hx6]
  have hx11A : rfA0.get .x11 = b := by
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
    exact hx11
  have hreadA : execBlock Region.empty ptr rfA0 wsA0
      [.LBU .x29 .x28 (0 : BitVec 12)] =
      (rfA0.set .x29 ((aBytes.getD i 0).zeroExtend 64), wsA0) := by
    apply execBlock_lbu_rw_div ptr rfA0 wsA0 aBytes i hiLt haddrA
    · rw [hws0eq]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [hwsState, hx11A]
    · exact hlenA
  have hwsSeq : wsS = (divState aBytes aBytes b i).1 := by
    rw [hwsA, execBlock_lbu_ws, hws0eq]
    exact hwsState
  have hx29S : rfS.get .x29 = (aBytes.getD i 0).zeroExtend 64 := by
    rw [hrfA, hreadA, RegFile.get_set_self _ _ _ (by decide)]
  have hx5S : rfS.get .x5 = (divState aBytes aBytes b i).2 := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _
      (by decide : Reg.x5 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx5
  have hx6S : rfS.get .x6 = BitVec.ofNat 64 i := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _
      (by decide : Reg.x6 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx6
  have hx11S : rfS.get .x11 = b := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _
      (by decide : Reg.x11 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hx12S : rfS.get .x12 = ptr := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _
      (by decide : Reg.x12 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12
  have hdiv := divStore_effect ptr rfS wsS i hiLt (aBytes.getD i 0) b
    (divState aBytes aBytes b i).2 hx29S hx5S hx6S hx11S hx12S
  dsimp only at hdiv
  obtain ⟨hsx10, hsx11, hsx12, hsx5, hsx6, hsws⟩ := hdiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hiLt, hbPos, hbBound, hlenA, hpl, ?_⟩
  · rw [hrf', hsx10, hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrf', hsx11]
  · rw [hrf', hsx12]
  · rw [hrf', hsx5, divState_succ]
  · rw [hrf', hsx6]
  · rw [hws', hsws, hwsSeq, divState_succ]
  · exact hA

private theorem u256DivU64BeInPlace_retVal_post (ptr b : Word)
    (aBytes : List (BitVec 8)) :
    ∀ rf ws A,
      sp Region.empty ⟨ptr, 32⟩ (.block "retVal" [.MV .x10 .x5])
        (u256DivU64BeInPlaceLoopPost ptr b aBytes) rf ws A →
      (u256DivU64BeInPlaceFn ptr b aBytes).post rf ws A := by
  rintro rf ws A ⟨rf₀, ws₀, hws₀, hloop, hrf, hws⟩
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsBytes, hA⟩ := hloop
  subst hrf
  subst hws
  simp only [u256DivU64BeInPlaceFn, execBlock_cons, execBlock_nil, execInstrRF,
    aluSem]
  refine ⟨?_, ?_, ?_, hwsBytes, hA⟩
  · rw [RegFile.get_set_self _ _ _ (by decide), hx5]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]

theorem u256DivU64BeInPlace_spec (ptr b : Word)
    (aBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨ptr, 32⟩)
    (base : Word) :
    (u256DivU64BeInPlaceFn ptr b aBytes).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case u256DivU64BeInPlace.loop.inv_init =>
    rintro rf ws A ⟨rfH, wsH, hwsH, hinit, hrf, hws⟩
    obtain ⟨rf₀, ws₀, hws₀, hpre, hrfH, hwsH_eq⟩ := hinit
    obtain ⟨hx10, hx11, hx12, hwsOrig, hbPos, hbBound, hlenA, hpl, hA⟩ := hpre
    dsimp only [u256DivU64BeInPlaceFn] at hws₀ hwsH hrfH hwsH_eq hrf hws
    subst hrf
    subst hws
    subst hrfH
    subst hwsH_eq
    unfold u256DivU64BeInPlaceInv
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hbPos, hbBound, hlenA,
      hpl, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · exact hwsOrig
  case u256DivU64BeInPlace.loop.inv_step =>
    rintro i hiLt rf' ws' A' hsp
    obtain ⟨rfB, wsB, hwsB, hbody, hrf', hws'⟩ := hsp
    dsimp only [u256DivU64BeInPlaceFn] at hbody hwsB hrf' hws'
    have hb := u256DivU64BeInPlaceLoopBody_effect ptr b aBytes i rfB wsB A' hbody
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hbPos, hbBound,
      hlenA, hpl, hA⟩ := hb
    subst hrf'
    subst hws'
    unfold u256DivU64BeInPlaceInv
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hbPos, hbBound, hlenA,
      hpl, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), hx5]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7), hx6]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · exact hwsState
  case u256DivU64BeInPlace.loop.exhausted =>
    rintro rf ws A hinv
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hiLe, hbPos,
      hbBound, hlenA, hpl, hA⟩ := hinv
    simp only [Cond.holds]
    rw [hx6, hx7]
    intro h_ne
    exact h_ne rfl
  case u256DivU64BeInPlace.loop.body.readA.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hguard⟩, hrf, hwsEq⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos,
      hbBound, hlenA, hpl, hA⟩ := hinv
    dsimp only [u256DivU64BeInPlaceFn] at hrf hws hws₀ hwsEq ⊢
    have hws32 : ws.length = 32 := hws
    subst hrf
    subst hwsEq
    have haddr : (rf₀.set Reg.x28 (rf₀.get Reg.x10 + rf₀.get Reg.x6)).get
        Reg.x28 = ptr + BitVec.ofNat 64 i := by
      rw [RegFile.get_set_self _ _ _ (by decide), hx10, hx6]
    exact readLbuRwDiv_blockVCs ptr _ ws i hi haddr hws32
  case u256DivU64BeInPlace.loop.body.divStore.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rfA, wsA, hwsA, hreach0, hrfA, hwsAeq⟩ := hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hguard⟩, hrf0, hws0eq⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos,
      hbBound, hlenA, hpl, hA⟩ := hinv
    dsimp only [u256DivU64BeInPlaceFn] at hrfA hrf0 hwsA hws0eq hws₀ hws ⊢
    have hws32 : ws.length = 32 := hws
    have hx6' : rf.get .x6 = BitVec.ofNat 64 i := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x29 .x28
        (0 : BitVec 12) .x6 (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx6]
    have hx12' : rf.get .x12 = ptr := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x29 .x28
        (0 : BitVec 12) .x12 (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx12]
    exact divStore_blockVCs ptr rf ws i hi hx6' hx12' hws32
  case u256DivU64BeInPlace.post =>
    intro rf ws A h
    unfold u256DivU64BeInPlaceFn u256DivU64BeInPlaceBody at h
    obtain ⟨rfLoop, wsLoop, hwsLoop, hloopExit, hrf, hws⟩ := h
    obtain ⟨⟨i, hiFuel, hinv⟩, hnotGuard⟩ := hloopExit
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos,
      hbBound, hlenA, hpl, hA⟩ := hinv
    have heq : rfLoop.get .x6 = rfLoop.get .x7 := by
      by_contra h_ne
      exact hnotGuard h_ne
    have hiEq : i = 32 := by
      have hto := congrArg BitVec.toNat heq
      have hiToNat : (BitVec.ofNat 64 i).toNat = i := by
        rw [BitVec.toNat_ofNat]
        omega
      rw [hx6, hx7, hiToNat,
        show ((32 : Word).toNat = 32) from by decide] at hto
      omega
    subst hiEq
    subst hrf
    subst hws
    unfold u256DivU64BeInPlaceFn
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]
    · exact hwsState
    · exact hA

theorem u256DivU64BeInPlaceFlat_spec (ret ptr b : Word)
    (aBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨ptr, 32⟩)
    (hlen : aBytes.length = 32)
    (hptr : ptr.toNat + 32 < 2 ^ 64)
    (hbPos : 0 < b.toNat)
    (hbBound : b.toNat ≤ 2 ^ 56)
    (hsz : 4 * ((u256DivU64BeInPlaceFn ptr b aBytes).body.size + 1)
      ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((u256DivU64BeInPlaceFn ptr b aBytes).body.steps + 1)
      (GuestAddrs.u256_div_u64_be : Word) ret u256DivU64BeCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ b) **
        (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr aBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        (.x10 ↦ᵣ u256DivU64BeRemainder aBytes aBytes b) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes b)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns u256DivU64BeScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ ptr) ** bytesRegion ptr aBytes)
      (fun vf => ?_))
  have hpre : (u256DivU64BeInPlaceFn ptr b aBytes).pre
      (fun r => if r = .x10 then ptr else
        if r = .x11 then b else if r = .x12 then ptr else vf r)
      aBytes empAssertion := by
    refine ⟨?_, ?_, ?_, rfl, hbPos, hbBound, hlen, hptr, rfl⟩
    · show RegFile.get _ .x10 = ptr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = b
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = ptr
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := @Fn.retSpecFlat
    (u256DivU64BeInPlaceFn ptr b aBytes)
    (GuestAddrs.u256_div_u64_be : Word)
    (u256DivU64BeInPlace_spec ptr b aBytes hrw
      (GuestAddrs.u256_div_u64_be : Word))
    hsz ret halign
    (fun r => if r = .x10 then ptr else
      if r = .x11 then b else if r = .x12 then ptr else vf r)
    aBytes (by simpa [u256DivU64BeInPlaceFn] using hlen) hpre
    (((.x10 ↦ᵣ u256DivU64BeRemainder aBytes aBytes b) **
          (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ ptr) **
          regOwns u256DivU64BeScratch) **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes b))
    (fun _ _ _ hpost => hpost.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hx10', hx11', hx12', hws', _hA⟩ := hpost
      subst ws'
      have g10 : rf' .x10 = u256DivU64BeRemainder aBytes aBytes b := by
        rw [← hx10', RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have g11 : rf' .x11 = b := by
        rw [← hx11', RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      have g12 : rf' .x12 = ptr := by
        rw [← hx12', RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_u256Div, g10, g11, g12] at hh
      rw [show (u256DivU64BeInPlaceFn ptr b aBytes).rw.base = ptr from rfl] at hh
      have hh1 :
          (((((((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder aBytes aBytes b) **
            (.x11 ↦ᵣ b)) ** (.x12 ↦ᵣ ptr)) **
            bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes b)) **
            regAtomsOf (fun r => rf' r) u256DivU64BeScratch) hp) := by
        xperm_hyp hh
      have hh2 := sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) u256DivU64BeScratch) hp hh1
      xperm_hyp hh2)
  rw [show (u256DivU64BeInPlaceFn ptr b aBytes).programRet
      (GuestAddrs.u256_div_u64_be : Word) = u256DivU64Be_prog from rfl] at had
  rw [show (u256DivU64BeInPlaceFn ptr b aBytes).region = Region.empty from rfl,
    show (u256DivU64BeInPlaceFn ptr b aBytes).rw.base = ptr from rfl,
    show Region.empty.base = (0 : Word) from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_u256Div,
    show (if (Reg.x10 : Reg) = .x10 then ptr else _) = ptr
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then ptr else
      if (Reg.x11 : Reg) = .x11 then b else _) = b from by
      rw [if_neg (by decide), if_pos rfl],
    show (if (Reg.x12 : Reg) = .x10 then ptr else
      if (Reg.x12 : Reg) = .x11 then b else
      if (Reg.x12 : Reg) = .x12 then ptr else _) = ptr from by
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl],
    regAtomsOf_congr
      (fun r => if r = .x10 then ptr else
        if r = .x11 then b else if r = .x12 then ptr else vf r)
      vf u256DivU64BeScratch
      (fun r hr => by
        obtain ⟨h10, h11, h12⟩ := u256Div_args_notin_scratch r hr
        show (if r = .x10 then ptr else
          if r = .x11 then b else if r = .x12 then ptr else vf r) = vf r
        rw [if_neg h10, if_neg h11, if_neg h12])] at had
  simp only [sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end U256DivU64BeSAsm

end EvmAsm.Codegen
