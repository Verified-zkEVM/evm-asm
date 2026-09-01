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

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256DivU64BeSAsm

/-! One restoring bit step.  `bit` and the returned quotient bit are 0/1
    words.  The high bit is captured before the shift because the shifted
    remainder is a 65-bit mathematical value even though the machine keeps
    its low 64 bits. -/
def divBitStep (bit b rem : Word) : Word × Word :=
  let high := rem >>> (63 : BitVec 6).toNat
  let shifted := (rem <<< (1 : BitVec 6).toNat) ||| bit
  let less := if BitVec.ult shifted b then (1 : Word) else 0
  let take := (less ^^^ 1) ||| high
  let mask := (0 : Word) - take
  (take, shifted - (b &&& mask))

def divByteStepAux (byte b rem q : Word) : Nat → Word × Word
  | 0 => (q, rem)
  | n + 1 =>
      let bit := (byte >>> (7 : BitVec 6).toNat) &&& (1 : Word)
      let step := divBitStep bit b rem
      divByteStepAux (byte <<< (1 : BitVec 6).toNat) b step.2
        ((q <<< (1 : BitVec 6).toNat) ||| step.1) n

/-! The full-width machine result for one byte.  Keeping the quotient in a
    word here makes the inner-loop invariant definitionally match x31; the
    byte-valued view below is only for the output memory model. -/
def divByteStepWord (byte : BitVec 8) (b rem : Word) : Word × Word :=
  divByteStepAux (BitVec.zeroExtend 64 byte) b rem 0 8

/-! One byte of big-endian restoring division, computed exactly as the RV64
    code does, with the quotient narrowed to the output byte. -/
def divByteStep (byte : BitVec 8) (b rem : Word) : BitVec 8 × Word :=
  let step := divByteStepWord byte b rem
  (step.1.truncate 8, step.2)

/-- Pure model of the loop after `k` processed big-endian bytes, walking from
    byte 0 to byte 31.  The state is `(outputBytes, remainder)`. -/
def divState (a orig : List (BitVec 8)) (b : Word) : Nat → List (BitVec 8) × Word
  | 0 => (orig, 0)
  | k + 1 =>
      let st := divState a orig b k
      let step := divByteStep (a.getD k 0) b st.2
      (st.1.set k step.1, step.2)

theorem divState_succ (a orig : List (BitVec 8)) (b : Word) (k : Nat) :
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
    0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧
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
    0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧
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
def u256DivU64BeInnerBody : Stmt :=
  .block "bit"
    [.SRLI .x28 .x5 (63 : BitVec 6),
     .SLLI .x5 .x5 (1 : BitVec 6),
     .SRLI .x30 .x29 (7 : BitVec 6),
     .ANDI .x30 .x30 (1 : BitVec 12),
     .SLLI .x29 .x29 (1 : BitVec 6),
     .OR .x5 .x5 .x30,
     .SLTU .x30 .x5 .x11,
     .XORI .x30 .x30 (1 : BitVec 12),
     .OR .x30 .x30 .x28,
     .SLLI .x31 .x31 (1 : BitVec 6),
     .OR .x31 .x31 .x30,
     .SUB .x28 .x0 .x30,
     .AND .x28 .x28 .x11,
     .SUB .x5 .x5 .x28,
     .ADDI .x7 .x7 (-1 : BitVec 12)]

def u256DivU64BeInnerInv (srcPtr outPtr b : Word)
    (i : Nat) (byte rem q : Word) (j : Nat)
    (srcBytes orig : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf ws A =>
    rf.get .x10 = srcPtr ∧ rf.get .x11 = b ∧ rf.get .x12 = outPtr ∧
    rf.get .x6 = BitVec.ofNat 64 i ∧
    rf.get .x5 = rem ∧
    rf.get .x29 = byte ∧
    rf.get .x7 = BitVec.ofNat 64 (8 - j) ∧
    rf.get .x31 = q ∧
    divByteStepAux byte b rem q (8 - j) =
      divByteStepWord (srcBytes.getD i 0)
        b (divState srcBytes orig b i).2 ∧
    ws = (divState srcBytes orig b i).1 ∧ j ≤ 8 ∧
    0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧
    srcBytes.length = 32 ∧ orig.length = 32 ∧
    srcPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
    (srcPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ srcPtr.toNat) ∧
    A = bytesRegion srcPtr srcBytes

def u256DivU64BeBitsInvS (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Nat →
      RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf₀ _ _ j rf ws A =>
    ∃ i byte rem q, i < 32 ∧
      rf₀.get .x6 = BitVec.ofNat 64 i ∧
      u256DivU64BeInnerInv srcPtr outPtr b i byte rem q j
        srcBytes orig rf ws A

def u256DivU64BeLoopBody (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "addrRead" [.ADD .x28 .x10 .x6] ;;;
  .readAt "readA" .x10 (roSrc srcPtr srcBytes) [.LBU .x29 .x28 (0 : BitVec 12)] ;;;
  .block "divInit" [.LI .x31 (0 : Word), .LI .x7 (8 : Word)] ;;;
  .«whileS» "bits" (.bne .x7 .x0) 8
    (u256DivU64BeBitsInvS srcPtr outPtr b srcBytes orig) u256DivU64BeInnerBody ;;;
  .block "divStore"
    [.ADD .x28 .x12 .x6,
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
    (u256DivU64BeLoopBody srcPtr outPtr b srcBytes orig) ;;;
  .block "retVal" [.MV .x10 .x5]

def u256DivU64BeFn (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) : Fn where
  name := "u256DivU64Be"
  region := Region.empty
  rw := ⟨outPtr, 32⟩
  pre := u256DivU64BePre srcPtr outPtr b srcBytes orig
  post := u256DivU64BePost srcPtr outPtr b srcBytes orig
  body := u256DivU64BeBody srcPtr outPtr b srcBytes orig

/-- A layout parameter changes the absolute anchors, but not the relative
    branch/jump displacements used by this routine. -/
private theorem u256DivU64Be_prog_of_layout_independent (L : GuestLayout) :
    u256DivU64Be_prog_of L = u256DivU64Be_prog_of (.zero) := by
  have h₁ : brOff (L.u256_div_u64_be + 116) (L.u256_div_u64_be + 12) =
      (104 : BitVec 13) := by
    unfold brOff
    rw [Nat.cast_add, Nat.cast_add]
    norm_num
    decide
  have h₂ : brOff (L.u256_div_u64_be + 100) (L.u256_div_u64_be + 32) =
      (68 : BitVec 13) := by
    unfold brOff
    rw [Nat.cast_add, Nat.cast_add]
    norm_num
    decide
  have h₃ : jalOff (L.u256_div_u64_be + 32) (L.u256_div_u64_be + 96) =
      (-64 : BitVec 21) := by
    unfold jalOff
    rw [Nat.cast_add, Nat.cast_add]
    norm_num
    decide
  have h₄ : jalOff (L.u256_div_u64_be + 8) (L.u256_div_u64_be + 112) =
      (-104 : BitVec 21) := by
    unfold jalOff
    rw [Nat.cast_add, Nat.cast_add]
    norm_num
    decide
  unfold u256DivU64Be_prog_of
  rw [h₁, h₂, h₃, h₄]
  simp [GuestLayout.zero, brOff, jalOff]

/-- Layout-independence interlock: the body flattens to `u256DivU64Be_prog_of
    L` for an ARBITRARY layout `L`, so the body cannot reference the layout.
    The preceding displacement lemma supplies the arithmetic cancellation. -/
theorem u256DivU64BeBody_flatten (L : GuestLayout) :
    (u256DivU64BeBody 0 0 1 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
      = u256DivU64Be_prog_of L := by
  rw [u256DivU64Be_prog_of_layout_independent]
  decide

private theorem u256DivU64BeFn_programRet_eq
    (srcPtr outPtr b : Word) (srcBytes orig : List (BitVec 8)) :
    (u256DivU64BeFn srcPtr outPtr b srcBytes orig).programRet
        (GuestAddrs.u256_div_u64_be : Word) = u256DivU64Be_prog := by
  change (u256DivU64BeBody 0 0 1 [] []).flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] =
        u256DivU64Be_prog_of guestLayout
  rw [u256DivU64BeBody_flatten guestLayout,
    u256DivU64Be_prog_of_layout_independent]

#guard (u256DivU64BeBody 0 0 1 [] []).flatten 0 =
  (u256DivU64BeBody 0 0 1 [] []).flatten 0x80000000


/-! ## Local proof helpers -/

private theorem nat_lt_32_toNat (i : Nat) (hi : i < 32) :
    (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat]
  omega

theorem add_idx_sub_self (ptr : Word) (i : Nat) (hi : i < 32) :
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

theorem execBlock_lbu_ws (ro : Region) (rwBase : Word) (rf : RegFile)
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

/-
private theorem u256DivU64BeLoopBody_effect (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨outPtr, 32⟩ (u256DivU64BeLoopBody srcPtr outPtr b srcBytes orig)
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
      0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧
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

 -/

private theorem divState_length_early
    (a orig : List (BitVec 8)) (b : Word) (k : Nat) :
    (divState a orig b k).1.length = orig.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [divState_succ]
      simp only [List.length_set, ih]

theorem divStore_effect_early (outPtr : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hx6 : rf.get .x6 = BitVec.ofNat 64 i)
    (hx12 : rf.get .x12 = outPtr) (_hws : ws.length = 32) :
    let r := execBlock Region.empty outPtr rf ws
      [.ADD .x28 .x12 .x6, .SB .x28 .x31 (0 : BitVec 12),
       .ADDI .x6 .x6 (1 : BitVec 12)]
    r.1.get .x10 = rf.get .x10 ∧
    r.1.get .x11 = rf.get .x11 ∧
    r.1.get .x12 = outPtr ∧
    r.1.get .x5 = rf.get .x5 ∧
    r.1.get .x6 = BitVec.ofNat 64 (i + 1) ∧
    r.2 = ws.set i (BitVec.truncate 8 (rf.get .x31)) := by
  dsimp only
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ (0 : BitVec 12) i (by
    simp only [RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hx12, hx6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    rw [show outPtr + BitVec.ofNat 64 i + (0 : Word) =
      outPtr + BitVec.ofNat 64 i by bv_omega]
    exact add_idx_sub_self outPtr i hi)]
  rw [execBlock_cons, execBlock_nil]
  simp only [execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true]
  refine ⟨trivial, trivial, hx12, trivial, ?_, ?_⟩
  · rw [hx6, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    bv_omega
  · rfl

private theorem u256DivU64BeLoopBody_effect (srcPtr outPtr b : Word)
    (srcBytes orig : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨outPtr, 32⟩
        (u256DivU64BeLoopBody srcPtr outPtr b srcBytes orig)
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
      0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧
      srcBytes.length = 32 ∧ orig.length = 32 ∧
      srcPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
      (srcPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ srcPtr.toNat) ∧
      A' = bytesRegion srcPtr srcBytes := by
  intro rf' ws' A' hsp
  unfold u256DivU64BeLoopBody at hsp
  obtain ⟨rfS, wsS, hwsS, hreachA, hrf', hws'⟩ := hsp
  obtain ⟨rfEntry, wsEntry, AEntry, hentry,
    ⟨j, hjLe, hbits⟩, hnot⟩ := hreachA
  obtain ⟨i0, byte, rem, q, hi0, hsnap, hinv⟩ := hbits
  obtain ⟨rfD, wsD, hwsD, hreachD, hrfEntry, hwsEntry⟩ := hentry
  obtain ⟨rfA0, wsA0, AA, robA, restA, hlenARead, hreach0, _hsatA,
    hroArel, hrfA, hwsA, hAeqA⟩ := hreachD
  obtain ⟨rf0, ws0, hws0, ⟨hinv0, _hguard0⟩, hrf0, hws0eq⟩ := hreach0
  obtain ⟨hx10_0, hx11_0, hx12_0, hx5_0, hx6_0, hx7_0, hwsState0,
    hiLe0, hbPos0, hbBound0, hlenA0, hlenO0, hplA0, hplO0, hdisjA0,
    hA0⟩ := hinv0
  dsimp only [u256DivU64BeFn] at hrfEntry hwsEntry hrfA hwsA hrf0 hws0eq
  have hsnapOuter : rfEntry.get .x6 = BitVec.ofNat 64 i := by
    rw [hrfEntry, hrfA]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      loadSem, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
    by_cases hload : inRw outPtr wsA0 (rfA0.get .x28 + signExtend12 (0 : BitVec 12)) 1
    · rw [if_pos hload, RegFile.get_set_ne _ _ _ _ (by decide : .x6 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true]
      exact hx6_0
    · rw [if_neg hload, RegFile.get_set_ne _ _ _ _ (by decide : .x6 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        ]
      exact hx6_0
  have hiEq : i0 = i := by
    have hEq := hsnap.symm.trans hsnapOuter
    have hNat := congrArg BitVec.toNat hEq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hNat
    rw [Nat.mod_eq_of_lt (by omega : i0 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)] at hNat
    exact hNat
  subst i0
  obtain ⟨hx10, hx11, hx12, hx6, hx5, hx29, hx7, hx31, haux, hwsState,
    hjLe', hbPos, hbBound, hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
  have hjEq : j = 8 := by
    simp only [Cond.holds] at hnot
    rw [hx7] at hnot
    have hj8 : j ≤ 8 := hjLe
    by_contra hne
    have hjLt : j < 8 := by omega
    have hne0 : (BitVec.ofNat 64 (8 - j)) ≠ (0 : Word) := by
      intro hz
      have hz' := congrArg BitVec.toNat hz
      have hlt : 8 - j < 2 ^ 64 := by omega
      change (8 - j) % 2 ^ 64 = 0 at hz'
      rw [Nat.mod_eq_of_lt hlt] at hz'
      omega
    exact hnot hne0
  subst hjEq
  have hq : q = (divByteStepWord (srcBytes.getD i 0)
      b (divState srcBytes orig b i).2).1 := by
    have h := congrArg Prod.fst haux
    simpa [divByteStepAux] using h
  have hrem : rem = (divByteStepWord (srcBytes.getD i 0) b
      (divState srcBytes orig b i).2).2 := by
    have h := congrArg Prod.snd haux
    simpa [divByteStepAux] using h
  have hwsLen : wsS.length = 32 := by
    simpa [hwsState, divState_length_early] using hlenO
  have hstore := divStore_effect_early outPtr
    rfS wsS i hi0 hx6 hx12 hwsLen
  dsimp only at hstore
  obtain ⟨hsx10, hsx11, hsx12, hsx5, hsx6, hsws⟩ := hstore
  dsimp only [RwRegion.base] at hrf' hws'
  subst hrf'
  subst hws'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hi0, hbPos, hbBound, hlenA, hlenO,
    hplA, hplO, hdisjA, ?_⟩
  · exact hsx10.trans hx10
  · exact hsx11.trans hx11
  · exact hsx12
  · calc
      _ = rfS.get .x5 := hsx5
      _ = rem := hx5
      _ = (divByteStepWord (srcBytes.getD i 0)
          b (divState srcBytes orig b i).2).2 := hrem
      _ = (divState srcBytes orig b (i + 1)).2 := by
        rw [divState_succ]
        rfl
  · exact hsx6
  · rw [hsws, hwsState, divState_succ]
    simp [divByteStep, divByteStepWord, hx31, hq]
  · exact hA

theorem divStore_blockVCs (outPtr : Word) (rf : RegFile) (ws : List (BitVec 8))
    (i : Nat) (hi : i < 32)
    (hx6 : rf.get .x6 = BitVec.ofNat 64 i)
    (hx12 : rf.get .x12 = outPtr)
    (hws : ws.length = 32) :
    blockVCs Region.empty outPtr rf ws
      [.ADD .x28 .x12 .x6,
       .SB .x28 .x31 (0 : BitVec 12),
       .ADDI .x6 .x6 (1 : BitVec 12)] := by
  simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF]
  simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true, inRw]
  rw [hx12, hx6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  rw [show outPtr + BitVec.ofNat 64 i + (0 : Word) = outPtr + BitVec.ofNat 64 i by bv_omega]
  rw [add_idx_sub_self outPtr i hi, hws]
  simp only [one_dvd, and_true, true_and]
  omega

theorem innerBit_effect (rwBase : Word) (rf : RegFile) (ws : List (BitVec 8))
    (byte rem q b count : Word)
    (hx11 : rf.get .x11 = b) (hx5 : rf.get .x5 = rem)
    (hx7 : rf.get .x7 = count)
    (hx29 : rf.get .x29 = byte) (hx31 : rf.get .x31 = q) :
    let r := execBlock Region.empty rwBase rf ws
      [.SRLI .x28 .x5 (63 : BitVec 6),
       .SLLI .x5 .x5 (1 : BitVec 6),
       .SRLI .x30 .x29 (7 : BitVec 6),
       .ANDI .x30 .x30 (1 : BitVec 12),
       .SLLI .x29 .x29 (1 : BitVec 6),
       .OR .x5 .x5 .x30,
       .SLTU .x30 .x5 .x11,
       .XORI .x30 .x30 (1 : BitVec 12),
       .OR .x30 .x30 .x28,
       .SLLI .x31 .x31 (1 : BitVec 6),
       .OR .x31 .x31 .x30,
       .SUB .x28 .x0 .x30,
       .AND .x28 .x28 .x11,
       .SUB .x5 .x5 .x28,
       .ADDI .x7 .x7 (-1 : BitVec 12)]
    let step := divBitStep ((byte >>> (7 : BitVec 6).toNat) &&& (1 : Word)) b rem
    r.1.get .x10 = rf.get .x10 ∧
    r.1.get .x11 = b ∧
    r.1.get .x12 = rf.get .x12 ∧
    r.1.get .x6 = rf.get .x6 ∧
    r.1.get .x5 = step.2 ∧
    r.1.get .x7 = count - (1 : Word) ∧
    r.1.get .x29 = byte <<< (1 : BitVec 6).toNat ∧
    r.1.get .x30 = step.1 ∧
    r.1.get .x31 = (q <<< (1 : BitVec 6).toNat) ||| step.1 ∧
    r.2 = ws := by
  dsimp only
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons, execBlock_nil]
  simp only [execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true, hx11, hx5, hx7, hx29, hx31]
  have hsign1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsignm1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  rw [hsign1, hsignm1]
  simp [RegFile.get, divBitStep, BitVec.and_comm] ; bv_omega

private theorem divStore_effect (outPtr : Word) (rf : RegFile) (ws : List (BitVec 8))
    (i : Nat) (hi : i < 32)
    (hx6 : rf.get .x6 = BitVec.ofNat 64 i)
    (hx12 : rf.get .x12 = outPtr)
    (_hx31 : rf.get .x31 = (rf.get .x31))
    (_hws : ws.length = 32) :
    let r := execBlock Region.empty outPtr rf ws
      [.ADD .x28 .x12 .x6,
       .SB .x28 .x31 (0 : BitVec 12),
       .ADDI .x6 .x6 (1 : BitVec 12)]
    r.1.get .x10 = rf.get .x10 ∧
    r.1.get .x11 = rf.get .x11 ∧
    r.1.get .x12 = outPtr ∧
    r.1.get .x5 = rf.get .x5 ∧
    r.1.get .x6 = BitVec.ofNat 64 (i + 1) ∧
    r.2 = ws.set i (BitVec.truncate 8 (rf.get .x31)) := by
  dsimp only
  rw [execBlock_cons]
  simp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ (0 : BitVec 12) i (by
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
    rw [hx12, hx6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    rw [show outPtr + BitVec.ofNat 64 i + (0 : Word) = outPtr + BitVec.ofNat 64 i by bv_omega]
    exact add_idx_sub_self outPtr i hi)]
  rw [execBlock_cons, execBlock_nil]
  simp only [execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]
  refine ⟨trivial, trivial, ?_, trivial, ?_, ?_⟩
  · exact hx12
  · rw [hx6, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    bv_omega
  · rfl

private theorem u256DivU64BeInnerLoopBody_effect
    (srcPtr outPtr b : Word) (srcBytes orig : List (BitVec 8)) (j : Nat) :
    ∀ rf₀ ws₀ A₀ rf' ws' A',
      sp Region.empty ⟨outPtr, 32⟩ u256DivU64BeInnerBody
        (fun rf ws A =>
          u256DivU64BeBitsInvS srcPtr outPtr b srcBytes orig
            rf₀ ws₀ A₀ j rf ws A ∧
          Cond.holds (.bne .x7 .x0) rf) rf' ws' A' →
      u256DivU64BeBitsInvS srcPtr outPtr b srcBytes orig
        rf₀ ws₀ A₀ (j + 1) rf' ws' A' := by
  intro rf₀ ws₀ A₀ rf' ws' A' hsp
  obtain ⟨rf, ws, hws, hpre, hrf', hws'⟩ := hsp
  obtain ⟨hbits, hguard⟩ := hpre
  obtain ⟨i, byte, rem, q, hi, hsnap, hinv⟩ := hbits
  obtain ⟨hx10, hx11, hx12, hx6, hx5, hx29, hx7, hx31, haux, hwsState,
    hjLe, hbPos, hbBound, hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
  have hjLt : j < 8 := by
    simp only [Cond.holds] at hguard
    rw [hx7] at hguard
    by_contra hnot
    have hj8 : j = 8 := by omega
    subst hj8
    exact hguard rfl
  have he := innerBit_effect
    ({ base := outPtr, len := 32 } : RwRegion).base rf ws byte rem q b
    (BitVec.ofNat 64 (8 - j)) hx11 hx5 hx7 hx29 hx31
  dsimp only at he
  refine ⟨i, byte <<< 1, (divBitStep ((byte >>> 7) &&& (1 : Word)) b rem).2,
    (q <<< 1) ||| (divBitStep ((byte >>> 7) &&& (1 : Word)) b rem).1,
    hi, hsnap, ?_⟩
  rcases he with ⟨hx10E, hx11E, hx12E, hx6E, hx5E, hx7E, hx29E,
    hx30E, hx31E, hwsE⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, by omega,
    hbPos, hbBound, hlenA, hlenO, hplA, hplO, hdisjA, hA⟩
  · rw [hrf']
    exact hx10E.trans hx10
  · rw [hrf']
    exact hx11
  · rw [hrf']
    exact hx12
  · rw [hrf']
    exact hx6
  · rw [hrf']
    exact hx5E
  · rw [hrf']
    exact hx29E
  · rw [hrf']
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
    rw [hx7]
    rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) by decide]
    have hnat : 8 - j = (8 - (j + 1)) + 1 := by omega
    rw [show BitVec.ofNat 64 (8 - j) =
      BitVec.ofNat 64 ((8 - (j + 1)) + 1) by rw [hnat]]
    exact by
      simp only [BitVec.ofNat_add]
      bv_omega
  · rw [hrf']
    exact hx31E
  · rw [show 8 - j = (8 - (j + 1)) + 1 by omega] at haux
    simpa [divByteStepAux] using haux
  · calc
      ws' = (execBlock Region.empty outPtr rf ws
        [Instr.SRLI .x28 .x5 63, .SLLI .x5 .x5 1, .SRLI .x30 .x29 7,
         .ANDI .x30 .x30 1, .SLLI .x29 .x29 1, .OR .x5 .x5 .x30,
         .SLTU .x30 .x5 .x11, .XORI .x30 .x30 1,
         .OR .x30 .x30 .x28, .SLLI .x31 .x31 1,
         .OR .x31 .x31 .x30, .SUB .x28 .x0 .x30,
         .AND .x28 .x28 .x11, .SUB .x5 .x5 .x28,
         .ADDI .x7 .x7 (-1 : BitVec 12)]).2 := hws'
      _ = ws := hwsE
      _ = (divState srcBytes orig b i).1 := hwsState

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
    obtain ⟨_rfEntry, _wsEntry, _AEntry, _hentry, ⟨j, _hj, hbits⟩, _hnot⟩ := hreach
    obtain ⟨i, _byte, _rem, _q, hi, _hsnap, hinv⟩ := hbits
    obtain ⟨_hx10, _hx11, hx12, hx6, _hx5, _hx29, _hx7, _hx31,
      _haux, _hwsState, _hjLe, _hbPos, _hbBound, _hlenA, _hlenO, _hplA,
      _hplO, _hdisjA, _hA⟩ := hinv
    exact divStore_blockVCs outPtr rf ws i hi hx6 hx12 hws
  case u256DivU64Be.loop.body.bits.inv_init =>
    rintro rf ws A hsp
    obtain ⟨rfD, wsD, hwsD, hreachD, hrf, hws⟩ := hsp
    obtain ⟨rfA0, wsA0, AA, robA, restA, hlenARead, hreach0, _hsatA,
      hroArel, hrfA, hwsA, hAeqA⟩ := hreachD
    obtain ⟨rf0, ws0, hws0, hreach0', hrf0, hws0eq⟩ := hreach0
    obtain ⟨i, hi, hrest0⟩ := hreach0'
    obtain ⟨hinv0, _hguard0⟩ := hrest0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hiLe, hbPos,
      hbBound, hlenA0, hlenO, hplA, hplO, hdisjA, hA0⟩ := hinv0
    obtain ⟨hptrA, hrobA, hrestA⟩ := hroArel
    dsimp only [u256DivU64BeFn] at hrf hws hrfA hwsA hrf0 hws0eq
    have hiLt : i < 32 := by
      simp only [Cond.holds] at _hguard0
      by_contra hnot
      have hi32 : i = 32 := by omega
      subst hi32
      rw [hx6, hx7] at _hguard0
      exact _hguard0 rfl
    have haddrA : rfA0.get .x28 = rfA0.get .x10 + BitVec.ofNat 64 i := by
      rw [hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rw [hx6]
    have hreadA : execBlock { base := rfA0.get .x10, bytes := robA } ({ base := outPtr, len := 32 } : RwRegion).base rfA0 wsA0
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
    have hx29D : rfD.get .x29 = (srcBytes.getD i 0).zeroExtend 64 := by
      rw [hrfA, hreadA, RegFile.get_set_self _ _ _ (by decide)]
    have hx10D : rfD.get .x10 = srcPtr := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx10
    have hx11D : rfD.get .x11 = b := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx11
    have hx12D : rfD.get .x12 = outPtr := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx12
    have hx5D : rfD.get .x5 = (divState srcBytes orig b i).2 := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx5
    have hx6D : rfD.get .x6 = BitVec.ofNat 64 i := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx6
    have hwsDState : wsD = (divState srcBytes orig b i).1 := by
      rw [hwsA, execBlock_lbu_ws, hws0eq]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      exact hwsState
    have hx10R : rf.get .x10 = srcPtr := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx10D
    have hx11R : rf.get .x11 = b := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx11D
    have hx12R : rf.get .x12 = outPtr := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx12D
    have hx5R : rf.get .x5 = (divState srcBytes orig b i).2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx5D
    have hx6R : rf.get .x6 = BitVec.ofNat 64 i := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx6D
    have hx29R : rf.get .x29 = (srcBytes.getD i 0).zeroExtend 64 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx29D
    have hx7R : rf.get .x7 = (8 : Word) := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
    have hx31R : rf.get .x31 = (0 : Word) := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
    have hwsR : ws = (divState srcBytes orig b i).1 := by
      rw [hws, hwsDState]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    have hABytes : A = bytesRegion srcPtr srcBytes := by
      rw [hAeqA, hptrA, hrobA, hrestA]
      exact sepConj_emp_right' _
    refine ⟨i, (srcBytes.getD i 0).zeroExtend 64,
      (divState srcBytes orig b i).2, 0, hiLt, hx6R, ?_⟩
    refine ⟨hx10R, hx11R, hx12R, hx6R, hx5R,
      hx29R, hx7R, hx31R, ?_, hwsR, by omega,
      hbPos, hbBound, hlenA0, hlenO, hplA, hplO, hdisjA, hABytes⟩
    rfl
  case u256DivU64Be.loop.body.bits.inv_step =>
    rintro rf₀ ws₀ A₀ hreach i hiLt rf' ws' A' hsp
    exact u256DivU64BeInnerLoopBody_effect srcPtr outPtr b srcBytes orig i
      rf₀ ws₀ A₀ rf' ws' A' hsp
  case u256DivU64Be.loop.body.bits.exhausted =>
    rintro rf₀ ws₀ A₀ hreach rf ws A hbits
    obtain ⟨i, byte, rem, q, hi, hsnap, hinv⟩ := hbits
    obtain ⟨hx10, hx11, hx12, hx6, hx5, hx29, hx7, hx31, haux, hwsState,
      hjLe, hbPos, hbBound, hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hinv
    simp only [Cond.holds]
    rw [hx7]
    intro h_ne
    have hzero : (BitVec.ofNat 64 (8 - 8) : Word) = 0 := by decide
    exact h_ne hzero
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

theorem exposedRegs_split_u256Div (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
          (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf u256DivU64BeScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [u256DivU64BeScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

theorem u256Div_args_notin_scratch :
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
  have hbBound : b.toNat < 2 ^ 64 := by omega
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
  rw [u256DivU64BeFn_programRet_eq srcPtr outPtr b srcBytes orig] at had
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


end U256DivU64BeSAsm

end EvmAsm.Codegen
