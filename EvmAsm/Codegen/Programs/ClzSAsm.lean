/-
  EvmAsm.Codegen.Programs.ClzSAsm

  Verified SAsm body for the EIP-7939 CLZ dispatcher handler (the
  drop-in replacement for the raw `clzTail` string): load the four
  dwords of the top stack cell at `a2` in one focus block, select the
  highest nonzero limb with a 4-way ite cascade (summarized by an
  `.assert` join), narrow **branchlessly** (SRLI/SLTIU/SLLI/ADD/SLL —
  no `when`-disjunction), and store `(clz, 0, 0, 0)` back through a
  second focus block.  `clzFn_spec` is the machine-level correctness
  proof (`Fn.Spec` over the RV64 step function); the pure model
  `clz256` is pinned to ground truth by exhaustive single-bit `#guard`s
  below.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt

namespace ClzSAsm

def clzCellBytes (l0 l1 l2 l3 : Word) : List (BitVec 8) :=
  dwordBytes l0 ++ (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3))

@[simp] theorem length_clzCellBytes (l0 l1 l2 l3 : Word) :
    (clzCellBytes l0 l1 l2 l3).length = 32 := by
  simp [clzCellBytes]

theorem clzCell_dword0 (l0 l1 l2 l3 : Word) :
    packBytes (((clzCellBytes l0 l1 l2 l3).drop 0).take 8) = l0 :=
  packDword_at0 ..

theorem clzCell_drop8 (l0 l1 l2 l3 : Word) :
    (clzCellBytes l0 l1 l2 l3).drop 8
      = dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3) := by
  have h := drop8_dword_append l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) 0
  simp only [Nat.add_zero, List.drop_zero] at h
  rw [clzCellBytes, h]

theorem clzCell_dword1 (l0 l1 l2 l3 : Word) :
    packBytes (((clzCellBytes l0 l1 l2 l3).drop 8).take 8) = l1 := by
  rw [clzCell_drop8, take8_dword_append, packBytes_dwordBytes]

theorem clzCell_drop16 (l0 l1 l2 l3 : Word) :
    (clzCellBytes l0 l1 l2 l3).drop 16 = dwordBytes l2 ++ dwordBytes l3 := by
  have h1 := drop8_dword_append l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) 8
  have h2 := drop8_dword_append l1 (dwordBytes l2 ++ dwordBytes l3) 0
  simp only [Nat.reduceAdd] at h1
  simp only [Nat.add_zero, List.drop_zero] at h2
  rw [clzCellBytes, h1, h2]

theorem clzCell_dword2 (l0 l1 l2 l3 : Word) :
    packBytes (((clzCellBytes l0 l1 l2 l3).drop 16).take 8) = l2 := by
  rw [clzCell_drop16, take8_dword_append, packBytes_dwordBytes]

theorem clzCell_drop24 (l0 l1 l2 l3 : Word) :
    (clzCellBytes l0 l1 l2 l3).drop 24 = dwordBytes l3 := by
  have h1 := drop8_dword_append l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) 16
  have h2 := drop8_dword_append l1 (dwordBytes l2 ++ dwordBytes l3) 8
  have h3 := drop8_dword_append l2 (dwordBytes l3) 0
  simp only [Nat.reduceAdd] at h1 h2
  simp only [Nat.add_zero, List.drop_zero] at h3
  rw [clzCellBytes, h1, h2, h3]

theorem clzCell_dword3 (l0 l1 l2 l3 : Word) :
    packBytes (((clzCellBytes l0 l1 l2 l3).drop 24).take 8) = l3 := by
  rw [clzCell_drop24, List.take_of_length_le (by rw [length_dwordBytes]),
    packBytes_dwordBytes]

theorem clzCell_set0 (l0 l1 l2 l3 v : Word) :
    setBytes (clzCellBytes l0 l1 l2 l3) 0 (dwordBytes v)
      = clzCellBytes v l1 l2 l3 := by
  rw [clzCellBytes, setBytes_dword_at0, clzCellBytes]

theorem clzCell_set8 (l0 l1 l2 l3 v : Word) :
    setBytes (clzCellBytes l0 l1 l2 l3) 8 (dwordBytes v)
      = clzCellBytes l0 v l2 l3 := by
  have h1 := setBytes_dword_past l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) (dwordBytes v) 0
  simp only [Nat.add_zero] at h1
  rw [clzCellBytes, h1, setBytes_dword_at0, clzCellBytes]

theorem clzCell_set16 (l0 l1 l2 l3 v : Word) :
    setBytes (clzCellBytes l0 l1 l2 l3) 16 (dwordBytes v)
      = clzCellBytes l0 l1 v l3 := by
  have h1 := setBytes_dword_past l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) (dwordBytes v) 8
  have h2 := setBytes_dword_past l1
    (dwordBytes l2 ++ dwordBytes l3) (dwordBytes v) 0
  simp only [Nat.reduceAdd] at h1
  simp only [Nat.add_zero] at h2
  rw [clzCellBytes, h1, h2, setBytes_dword_at0, clzCellBytes]

theorem clzCell_set24 (l0 l1 l2 l3 v : Word) :
    setBytes (clzCellBytes l0 l1 l2 l3) 24 (dwordBytes v)
      = clzCellBytes l0 l1 l2 v := by
  have h1 := setBytes_dword_past l0
    (dwordBytes l1 ++ (dwordBytes l2 ++ dwordBytes l3)) (dwordBytes v) 16
  have h2 := setBytes_dword_past l1
    (dwordBytes l2 ++ dwordBytes l3) (dwordBytes v) 8
  have h3 := setBytes_dword_past l2 (dwordBytes l3) (dwordBytes v) 0
  simp only [Nat.reduceAdd] at h1 h2
  simp only [Nat.add_zero] at h3
  rw [clzCellBytes, h1, h2, h3, setBytes_dword_full _ _ (length_dwordBytes l3),
    clzCellBytes]

def clz64Step (x acc : Word) (probeShift amountShift : Nat) : Word × Word :=
  let probe := x >>> probeShift
  let cond : Word := if BitVec.ult probe (signExtend12 (1 : BitVec 12)) then 1 else 0
  let amount := cond <<< amountShift
  (x <<< (amount.toNat % 64), acc + amount)

def clz64Step32 (x acc : Word) : Word × Word :=
  clz64Step x acc 32 5

def clz64Step16 (x acc : Word) : Word × Word :=
  clz64Step x acc 48 4

def clz64Step8 (x acc : Word) : Word × Word :=
  clz64Step x acc 56 3

def clz64Step4 (x acc : Word) : Word × Word :=
  clz64Step x acc 60 2

def clz64Step2 (x acc : Word) : Word × Word :=
  clz64Step x acc 62 1

def clz64Step1 (x acc : Word) : Word :=
  let probe := x >>> 63
  let cond : Word := if BitVec.ult probe (signExtend12 (1 : BitVec 12)) then 1 else 0
  acc + cond

def clz64From (x acc : Word) : Word :=
  let (x, acc) := clz64Step32 x acc
  let (x, acc) := clz64Step16 x acc
  let (x, acc) := clz64Step8 x acc
  let (x, acc) := clz64Step4 x acc
  let (x, acc) := clz64Step2 x acc
  clz64Step1 x acc

def clzSelectedLimb (l0 l1 l2 l3 : Word) : Word :=
  if l3 ≠ 0 then l3
  else if l2 ≠ 0 then l2
  else if l1 ≠ 0 then l1
  else if l0 ≠ 0 then l0
  else 0

def clzSelectedAcc (l0 l1 l2 l3 : Word) : Word :=
  if l3 ≠ 0 then 0
  else if l2 ≠ 0 then 64
  else if l1 ≠ 0 then 128
  else if l0 ≠ 0 then 192
  else 193

def clz256 (l0 l1 l2 l3 : Word) : Word :=
  clz64From (clzSelectedLimb l0 l1 l2 l3) (clzSelectedAcc l0 l1 l2 l3)

-- The model against ground truth (`256 - bit_length`), exhaustively over
-- all 256 single-bit values, all "solid" values (top bit at i, all lower
-- bits set), and the edges.  This pins `clz64From`'s branchless steps to
-- what CLZ means, independently of the machine code.
#guard clz256 0 0 0 0 = (256 : Word)
#guard clz256 (BitVec.allOnes 64) (BitVec.allOnes 64) (BitVec.allOnes 64)
  (BitVec.allOnes 64) = 0
#guard (List.range 64).all fun i =>
  clz256 (1 <<< i : Word) 0 0 0 = BitVec.ofNat 64 (255 - i)
#guard (List.range 64).all fun i =>
  clz256 0 (1 <<< i : Word) 0 0 = BitVec.ofNat 64 (191 - i)
#guard (List.range 64).all fun i =>
  clz256 0 0 (1 <<< i : Word) 0 = BitVec.ofNat 64 (127 - i)
#guard (List.range 64).all fun i =>
  clz256 0 0 0 (1 <<< i : Word) = BitVec.ofNat 64 (63 - i)
#guard (List.range 64).all fun i =>
  clz256 ((1 <<< i : Word) ||| ((1 <<< i) - 1)) 0 0 0
    = BitVec.ofNat 64 (255 - i)
#guard (List.range 64).all fun i =>
  clz256 (BitVec.allOnes 64) (BitVec.allOnes 64) (BitVec.allOnes 64)
    ((1 <<< i : Word) ||| ((1 <<< i) - 1)) = BitVec.ofNat 64 (63 - i)

def clzLoadR (p l0 l1 l2 l3 : Word) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _A win rest =>
    rf.get .x12 = p ∧ win = clzCellBytes l0 l1 l2 l3 ∧
      rest = ⌜RwRegion.wf ⟨p, 32⟩⌝

def clzStoreR (p l0 l1 l2 l3 : Word) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _A win rest =>
    rf.get .x12 = p ∧ win = clzCellBytes l0 l1 l2 l3 ∧
      rest = ⌜RwRegion.wf ⟨p, 32⟩⌝

def clzLoadBlock : List Instr :=
  [.LD .x5 .x12 0, .LD .x6 .x12 8, .LD .x7 .x12 16, .LD .x14 .x12 24]

def clzStoreBlock : List Instr :=
  [.SD .x12 .x15 0, .SD .x12 .x0 8, .SD .x12 .x0 16, .SD .x12 .x0 24]

def clzNarrowBlock : List Instr :=
  [.SRLI .x16 .x14 32, .SLTIU .x17 .x16 1, .SLLI .x17 .x17 5,
    .ADD .x15 .x15 .x17, .SLL .x14 .x14 .x17,
   .SRLI .x16 .x14 48, .SLTIU .x17 .x16 1, .SLLI .x17 .x17 4,
    .ADD .x15 .x15 .x17, .SLL .x14 .x14 .x17,
   .SRLI .x16 .x14 56, .SLTIU .x17 .x16 1, .SLLI .x17 .x17 3,
    .ADD .x15 .x15 .x17, .SLL .x14 .x14 .x17,
   .SRLI .x16 .x14 60, .SLTIU .x17 .x16 1, .SLLI .x17 .x17 2,
    .ADD .x15 .x15 .x17, .SLL .x14 .x14 .x17,
   .SRLI .x16 .x14 62, .SLTIU .x17 .x16 1, .SLLI .x17 .x17 1,
    .ADD .x15 .x15 .x17, .SLL .x14 .x14 .x17,
   .SRLI .x16 .x14 63, .SLTIU .x16 .x16 1, .ADD .x15 .x15 .x16]

def clzNarrowBody : Stmt :=
  .block "narrow" clzNarrowBlock

/-- Register summary after the load block. -/
def clzLoaded (p pc aux1 aux3 l0 l1 l2 l3 : Word) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ A =>
    rf.get .x10 = pc ∧ rf.get .x11 = aux1 ∧ rf.get .x12 = p ∧
    rf.get .x13 = aux3 ∧ rf.get .x5 = l0 ∧ rf.get .x6 = l1 ∧
    rf.get .x7 = l2 ∧ rf.get .x14 = l3 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (clzCellBytes l0 l1 l2 l3))

/-- Register summary after the limb-select cascade. -/
def clzSelected (p pc aux1 aux3 l0 l1 l2 l3 : Word) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ A =>
    rf.get .x10 = pc ∧ rf.get .x11 = aux1 ∧ rf.get .x12 = p ∧
    rf.get .x13 = aux3 ∧
    rf.get .x14 = clzSelectedLimb l0 l1 l2 l3 ∧
    rf.get .x15 = clzSelectedAcc l0 l1 l2 l3 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (clzCellBytes l0 l1 l2 l3))

/-- Register summary after the branchless narrowing. -/
def clzComputed (p pc aux1 aux3 l0 l1 l2 l3 : Word) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ A =>
    rf.get .x10 = pc ∧ rf.get .x11 = aux1 ∧ rf.get .x12 = p ∧
    rf.get .x13 = aux3 ∧ rf.get .x15 = clz256 l0 l1 l2 l3 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (clzCellBytes l0 l1 l2 l3))

/-- The limb-select cascade, with the SAME `.assert` summary at the tail
    of every branch (the branch-tail summary idiom, docs/sasm-howto.md):
    each assert VC sees only its own linear path, and the downstream
    narrowing recovers `clzSelected` via `Stmt.sp_of_endsWith` with zero
    case analysis.  Asserts emit no code — `clz_verified` is unchanged. -/
def clzSelectBody (p pc aux1 aux3 l0 l1 l2 l3 : Word) : Stmt :=
  have sel : Stmt := .assert "sel" (clzSelected p pc aux1 aux3 l0 l1 l2 l3)
  .ite "limb3" (.bne .x14 .x0)
    (.block "off0" [.LI .x15 0] ;;; sel)
    (.block "limb2" [.MV .x14 .x7, .LI .x15 64] ;;;
      .ite "limb2nz" (.bne .x14 .x0)
        sel
        (.block "limb1" [.MV .x14 .x6, .LI .x15 128] ;;;
          .ite "limb1nz" (.bne .x14 .x0)
            sel
            (.block "limb0" [.MV .x14 .x5, .LI .x15 192] ;;;
              .ite "limb0nz" (.bne .x14 .x0)
                sel
                (.block "zero" [.LI .x15 193] ;;; sel))))

def clzBody (p pc aux1 aux3 l0 l1 l2 l3 : Word) : Stmt :=
  .blockAt "load" .x12 (clzLoadR p l0 l1 l2 l3) clzLoadBlock ;;;
  .assert "loaded" (clzLoaded p pc aux1 aux3 l0 l1 l2 l3) ;;;
  clzSelectBody p pc aux1 aux3 l0 l1 l2 l3 ;;;
  clzNarrowBody ;;;
  .assert "computed" (clzComputed p pc aux1 aux3 l0 l1 l2 l3) ;;;
  .blockAt "store" .x12
    (clzStoreR p l0 l1 l2 l3) clzStoreBlock

def clzFn (p pc aux1 aux3 l0 l1 l2 l3 : Word) : Fn where
  name := "clz"
  pre := fun rf _ A =>
    rf.get .x10 = pc ∧ rf.get .x11 = aux1 ∧ rf.get .x12 = p ∧
    rf.get .x13 = aux3 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ ** bytesRegion p (clzCellBytes l0 l1 l2 l3))
  post := fun rf _ A =>
    rf.get .x10 = pc ∧
    rf.get .x11 = aux1 ∧
    rf.get .x12 = p ∧
    rf.get .x13 = aux3 ∧
    A = (⌜RwRegion.wf ⟨p, 32⟩⌝ **
      bytesRegion p (clzCellBytes (clz256 l0 l1 l2 l3) 0 0 0))
  body := clzBody p pc aux1 aux3 l0 l1 l2 l3

def clz_verified : Program :=
  (clzBody 0 0 0 0 0 0 0 0).flatten 0

#guard (clz_verified : List Instr).length = 52

-- Position independence (the handler is emitted at a dispatcher label,
-- not a fixed address): flattening at any base yields the same code.
#guard ((clzBody 0 0 0 0 0 0 0 0).flatten 0
  = (clzBody 0 0 0 0 0 0 0 0).flatten 0x80000000)

private theorem clz_off (b : Word) (ofs : BitVec 12) (k : Nat)
    (hofs : signExtend12 ofs = BitVec.ofNat 64 k) (hk : k < 2 ^ 12) :
    ((b + signExtend12 ofs) - b).toNat = k := by
  rw [hofs]
  bv_omega

private theorem clz_load_engine (reg : Region) (rf : RegFile)
    (l0 l1 l2 l3 : Word) :
    execBlock reg (rf.get .x12) rf (clzCellBytes l0 l1 l2 l3) clzLoadBlock
      = ((((rf.set .x5 l0).set .x6 l1).set .x7 l2).set .x14 l3,
         clzCellBytes l0 l1 l2 l3) := by
  have h0 := clz_off (rf.get .x12) 0 0 (by decide) (by decide)
  have hx12a : (rf.set .x5 l0).get .x12 = rf.get .x12 :=
    RegFile.get_set_ne _ _ _ _ (by decide)
  have hx12b : ((rf.set .x5 l0).set .x6 l1).get .x12 = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12a]
  have hx12c : (((rf.set .x5 l0).set .x6 l1).set .x7 l2).get .x12
      = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12b]
  rw [show clzLoadBlock = [.LD .x5 .x12 0, .LD .x6 .x12 8,
      .LD .x7 .x12 16, .LD .x14 .x12 24] from rfl]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 0 l0
    h0 (by simp) (clzCell_dword0 ..)]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 8 l1
    (by rw [hx12a]; exact clz_off _ 8 8 (by decide) (by decide))
    (by simp) (clzCell_dword1 ..)]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 16 l2
    (by rw [hx12b]; exact clz_off _ 16 16 (by decide) (by decide))
    (by simp) (clzCell_dword2 ..)]
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ 24 l3
    (by rw [hx12c]; exact clz_off _ 24 24 (by decide) (by decide))
    (by simp) (clzCell_dword3 ..)]
  rfl

private theorem clz_load_blockVCs (reg : Region) (rf : RegFile)
    (l0 l1 l2 l3 : Word) :
    blockVCs reg (rf.get .x12) rf (clzCellBytes l0 l1 l2 l3) clzLoadBlock := by
  have h0 := clz_off (rf.get .x12) 0 0 (by decide) (by decide)
  have hx12a : (rf.set .x5 l0).get .x12 = rf.get .x12 :=
    RegFile.get_set_ne _ _ _ _ (by decide)
  have hx12b : ((rf.set .x5 l0).set .x6 l1).get .x12 = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12a]
  have hx12c : (((rf.set .x5 l0).set .x6 l1).set .x7 l2).get .x12
      = rf.get .x12 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx12b]
  have h8 := clz_off (rf.get .x12) 8 8 (by decide) (by decide)
  have h16 := clz_off (rf.get .x12) 16 16 (by decide) (by decide)
  have h24 := clz_off (rf.get .x12) 24 24 (by decide) (by decide)
  simp only [clzLoadBlock, blockVCs, loadSem,
    execInstrRF_ld_dword _ _ _ _ _ _ _ 0 l0 h0 (by simp) (clzCell_dword0 ..),
    execInstrRF_ld_dword _ _ _ _ _ _ _ 8 l1
      (by rw [hx12a]; exact h8) (by simp) (clzCell_dword1 ..),
    execInstrRF_ld_dword _ _ _ _ _ _ _ 16 l2
      (by rw [hx12b]; exact h16) (by simp) (clzCell_dword2 ..),
    hx12a, hx12b, hx12c, inRw, Region.loadOk, length_clzCellBytes,
    h0, h8, h16, h24]
  and_intros <;> trivial

private theorem clz_store_engine (reg : Region) (rf : RegFile)
    (l0 l1 l2 l3 : Word) :
    execBlock reg (rf.get .x12) rf (clzCellBytes l0 l1 l2 l3) clzStoreBlock
      = (rf, clzCellBytes (rf.get .x15) 0 0 0) := by
  have h0 := clz_off (rf.get .x12) 0 0 (by decide) (by decide)
  have h8 := clz_off (rf.get .x12) 8 8 (by decide) (by decide)
  have h16 := clz_off (rf.get .x12) 16 16 (by decide) (by decide)
  have h24 := clz_off (rf.get .x12) 24 24 (by decide) (by decide)
  rw [show clzStoreBlock = [.SD .x12 .x15 0, .SD .x12 .x0 8,
      .SD .x12 .x0 16, .SD .x12 .x0 24] from rfl]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 0 h0]
  rw [clzCell_set0]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 8 h8]
  rw [RegFile.get_x0, clzCell_set8]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 16 h16]
  rw [RegFile.get_x0, clzCell_set16]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 24 h24]
  rw [RegFile.get_x0, clzCell_set24]
  rfl

private theorem clz_store_blockVCs (reg : Region) (rf : RegFile)
    (l0 l1 l2 l3 : Word) :
    blockVCs reg (rf.get .x12) rf (clzCellBytes l0 l1 l2 l3) clzStoreBlock := by
  have h0 := clz_off (rf.get .x12) 0 0 (by decide) (by decide)
  have h8 := clz_off (rf.get .x12) 8 8 (by decide) (by decide)
  have h16 := clz_off (rf.get .x12) 16 16 (by decide) (by decide)
  have h24 := clz_off (rf.get .x12) 24 24 (by decide) (by decide)
  simp only [clzStoreBlock, blockVCs, loadSem, storeSem,
    execInstrRF_sd_dword _ _ _ _ _ _ _ 0 h0,
    execInstrRF_sd_dword _ _ _ _ _ _ _ 8 h8,
    execInstrRF_sd_dword _ _ _ _ _ _ _ 16 h16,
    inRw, length_clzCellBytes, length_setBytes, h0, h8, h16, h24]
  and_intros <;> trivial

private theorem clz_narrow_engine_x15 (reg : Region) (b : Word)
    (rf : RegFile) (ws : List (BitVec 8)) :
    (execBlock reg b rf ws clzNarrowBlock).1.get .x15
      = clz64From (rf.get .x14) (rf.get .x15) := by
  simp [clzNarrowBlock, clz64From, clz64Step32, clz64Step16, clz64Step8,
    clz64Step4, clz64Step2, clz64Step1, clz64Step, execBlock_cons,
    execBlock_nil, execInstrRF, aluSem, RegFile.get_set_self, RegFile.get_set_ne]

private theorem clz_narrow_engine_preserve_x10 (reg : Region) (b : Word)
    (rf : RegFile) (ws : List (BitVec 8)) :
    (execBlock reg b rf ws clzNarrowBlock).1.get .x10 = rf.get .x10 := by
  simp [clzNarrowBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne]

private theorem clz_narrow_engine_preserve_x11 (reg : Region) (b : Word)
    (rf : RegFile) (ws : List (BitVec 8)) :
    (execBlock reg b rf ws clzNarrowBlock).1.get .x11 = rf.get .x11 := by
  simp [clzNarrowBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne]

private theorem clz_narrow_engine_preserve_x12 (reg : Region) (b : Word)
    (rf : RegFile) (ws : List (BitVec 8)) :
    (execBlock reg b rf ws clzNarrowBlock).1.get .x12 = rf.get .x12 := by
  simp [clzNarrowBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne]

private theorem clz_narrow_engine_preserve_x13 (reg : Region) (b : Word)
    (rf : RegFile) (ws : List (BitVec 8)) :
    (execBlock reg b rf ws clzNarrowBlock).1.get .x13 = rf.get .x13 := by
  simp [clzNarrowBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne]

private theorem clz64From_zero_193 : clz64From 0 193 = (256 : Word) := by
  decide

-- The tiny ALU engines of the select cascade.
private theorem clz_li_engine (reg : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (imm : Word) :
    (execBlock reg b rf ws [.LI .x15 imm]).1 = rf.set .x15 imm := by
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]

private theorem clz_mvli_engine (reg : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (src : Reg) (imm : Word) :
    (execBlock reg b rf ws [.MV .x14 src, .LI .x15 imm]).1
      = (rf.set .x14 (rf.get src)).set .x15 imm := by
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]

private theorem clz_mvli_get_pres (rf : RegFile) (src : Reg) (imm : Word)
    (r : Reg) (h14 : r ≠ .x14) (h15 : r ≠ .x15) :
    ((rf.set .x14 (rf.get src)).set .x15 imm).get r = rf.get r := by
  rw [RegFile.get_set_ne _ _ _ _ h15, RegFile.get_set_ne _ _ _ _ h14]

private theorem clz_mvli_get_x14 (rf : RegFile) (src : Reg) (imm : Word) :
    ((rf.set .x14 (rf.get src)).set .x15 imm).get .x14 = rf.get src := by
  rw [RegFile.get_set_ne _ _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide)]

private theorem clz_mvli_get_x15 (rf : RegFile) (src : Reg) (imm : Word) :
    ((rf.set .x14 (rf.get src)).set .x15 imm).get .x15 = imm :=
  RegFile.get_set_self _ _ _ (by decide)

theorem clzFn_spec (p pc aux1 aux3 l0 l1 l2 l3 base : Word) :
    (clzFn p pc aux1 aux3 l0 l1 l2 l3).Spec base := by
  vcgen
  case clz.load.focus =>
    rintro rf ws A ⟨hx10, hx11, hx12, hx13, hA⟩ hApc hp hhp
    rw [hA] at hhp
    refine ⟨clzCellBytes l0 l1 l2 l3, ⌜RwRegion.wf ⟨p, 32⟩⌝,
      ⟨hx12, rfl, rfl⟩, ?_, pcFree_pure, ?_⟩
    · rw [hx12]
      xperm_hyp hhp
    · rw [hx12, length_clzCellBytes]
      exact ((sepConj_pure_left hp).mp hhp).1
  case clz.load.mem =>
    rintro rf ws A win rest - - ⟨hptr, rfl, rfl⟩ -
    exact clz_load_blockVCs _ rf l0 l1 l2 l3
  case clz.loaded =>
    refine Stmt.sp_blockAt_split _ _ ?_
    rintro rf ws A win rest - ⟨hx10, hx11, hx12, hx13, -⟩ - ⟨hptr, rfl, rfl⟩
    rw [clz_load_engine]
    unfold clzLoaded
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx10
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx11
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx12
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx13
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · rw [hx12, sepConj_comm']
  case clz.limb3.t.sel =>
    refine Stmt.sp_block_split _ _ ?_
    rintro rf ws A - ⟨⟨-, hL⟩, hc⟩
    obtain ⟨hx10, hx11, hx12, hx13, hx5, hx6, hx7, hx14, hA⟩ := hL
    simp only [Cond.holds, RegFile.get_x0, ne_eq] at hc
    rw [hx14] at hc
    have hsel : clzSelectedLimb l0 l1 l2 l3 = l3 := by
      unfold clzSelectedLimb
      rw [if_pos hc]
    have hacc : clzSelectedAcc l0 l1 l2 l3 = 0 := by
      unfold clzSelectedAcc
      rw [if_pos hc]
    rw [clz_li_engine]
    unfold clzSelected
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx10
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx11
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx12
    · rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx13
    · rw [RegFile.get_set_ne _ _ _ _ (by decide), hx14, hsel]
    · rw [RegFile.get_set_self _ _ _ (by decide), hacc]
  case clz.limb3.e.limb2nz.t.sel =>
    rintro rf ws A ⟨hblk, hc2⟩
    obtain ⟨rf₀, ws₀, -, ⟨⟨-, hL⟩, hn3⟩, hrf, -⟩ := hblk
    obtain ⟨hx10, hx11, hx12, hx13, hx5, hx6, hx7, hx14, hA⟩ := hL
    rw [clz_mvli_engine] at hrf
    simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hn3
    rw [hx14] at hn3
    simp only [Cond.holds, RegFile.get_x0, ne_eq] at hc2
    rw [hrf, clz_mvli_get_x14, hx7] at hc2
    have hsel : clzSelectedLimb l0 l1 l2 l3 = l2 := by
      unfold clzSelectedLimb
      rw [if_neg (by simp [hn3]), if_pos hc2]
    have hacc : clzSelectedAcc l0 l1 l2 l3 = 64 := by
      unfold clzSelectedAcc
      rw [if_neg (by simp [hn3]), if_pos hc2]
    subst hrf
    unfold clzSelected
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hA⟩
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx10
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx11
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx12
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx13
    · rw [clz_mvli_get_x14, hx7, hsel]
    · rw [clz_mvli_get_x15, hacc]
  case clz.limb3.e.limb2nz.e.limb1nz.t.sel =>
    rintro rf ws A ⟨hb1, hc1⟩
    obtain ⟨rf₁, ws₁, -, ⟨hb2, hn2⟩, hrf, -⟩ := hb1
    obtain ⟨rf₀, ws₀, -, ⟨⟨-, hL⟩, hn3⟩, hrf₁, -⟩ := hb2
    obtain ⟨hx10, hx11, hx12, hx13, hx5, hx6, hx7, hx14, hA⟩ := hL
    rw [clz_mvli_engine] at hrf₁
    rw [clz_mvli_engine] at hrf
    simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hn3 hn2
    rw [hx14] at hn3
    rw [hrf₁, clz_mvli_get_x14, hx7] at hn2
    simp only [Cond.holds, RegFile.get_x0, ne_eq] at hc1
    have hx6₁ : rf₁.get .x6 = l1 := by
      rw [hrf₁, clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hx6]
    rw [hrf, clz_mvli_get_x14, hx6₁] at hc1
    have hsel : clzSelectedLimb l0 l1 l2 l3 = l1 := by
      unfold clzSelectedLimb
      rw [if_neg (by simp [hn3]), if_neg (by simp [hn2]), if_pos hc1]
    have hacc : clzSelectedAcc l0 l1 l2 l3 = 128 := by
      unfold clzSelectedAcc
      rw [if_neg (by simp [hn3]), if_neg (by simp [hn2]), if_pos hc1]
    subst hrf
    unfold clzSelected
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hA⟩
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx10
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx11
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx12
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx13
    · rw [clz_mvli_get_x14, hx6₁, hsel]
    · rw [clz_mvli_get_x15, hacc]
  case clz.limb3.e.limb2nz.e.limb1nz.e.limb0nz.t.sel =>
    rintro rf ws A ⟨hb1, hc0⟩
    obtain ⟨rf₂, ws₂, -, ⟨hb2, hn1⟩, hrf, -⟩ := hb1
    obtain ⟨rf₁, ws₁, -, ⟨hb3, hn2⟩, hrf₂, -⟩ := hb2
    obtain ⟨rf₀, ws₀, -, ⟨⟨-, hL⟩, hn3⟩, hrf₁, -⟩ := hb3
    obtain ⟨hx10, hx11, hx12, hx13, hx5, hx6, hx7, hx14, hA⟩ := hL
    rw [clz_mvli_engine] at hrf₁
    rw [clz_mvli_engine] at hrf₂
    rw [clz_mvli_engine] at hrf
    simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hn3 hn2 hn1
    rw [hx14] at hn3
    rw [hrf₁, clz_mvli_get_x14, hx7] at hn2
    have hx6₁ : rf₁.get .x6 = l1 := by
      rw [hrf₁, clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hx6]
    rw [hrf₂, clz_mvli_get_x14, hx6₁] at hn1
    have hx5₂ : rf₂.get .x5 = l0 := by
      rw [hrf₂, clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hx5]
    simp only [Cond.holds, RegFile.get_x0, ne_eq] at hc0
    rw [hrf, clz_mvli_get_x14, hx5₂] at hc0
    have hsel : clzSelectedLimb l0 l1 l2 l3 = l0 := by
      unfold clzSelectedLimb
      rw [if_neg (by simp [hn3]), if_neg (by simp [hn2]),
        if_neg (by simp [hn1]), if_pos hc0]
    have hacc : clzSelectedAcc l0 l1 l2 l3 = 192 := by
      unfold clzSelectedAcc
      rw [if_neg (by simp [hn3]), if_neg (by simp [hn2]),
        if_neg (by simp [hn1]), if_pos hc0]
    subst hrf
    unfold clzSelected
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hA⟩
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx10
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx11
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx12
    · rw [clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx13
    · rw [clz_mvli_get_x14, hx5₂, hsel]
    · rw [clz_mvli_get_x15, hacc]
  case clz.limb3.e.limb2nz.e.limb1nz.e.limb0nz.e.sel =>
    refine Stmt.sp_block_split _ _ ?_
    rintro rf ws A - ⟨hb1, hn0⟩
    obtain ⟨rf₂, ws₂, -, ⟨hb2, hn1⟩, hrf, -⟩ := hb1
    obtain ⟨rf₁, ws₁, -, ⟨hb3, hn2⟩, hrf₂, -⟩ := hb2
    obtain ⟨rf₀, ws₀, -, ⟨⟨-, hL⟩, hn3⟩, hrf₁, -⟩ := hb3
    obtain ⟨hx10, hx11, hx12, hx13, hx5, hx6, hx7, hx14, hA⟩ := hL
    rw [clz_mvli_engine] at hrf₁
    rw [clz_mvli_engine] at hrf₂
    rw [clz_mvli_engine] at hrf
    simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hn3 hn2 hn1 hn0
    rw [hx14] at hn3
    rw [hrf₁, clz_mvli_get_x14, hx7] at hn2
    have hx6₁ : rf₁.get .x6 = l1 := by
      rw [hrf₁, clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hx6]
    rw [hrf₂, clz_mvli_get_x14, hx6₁] at hn1
    have hx5₂ : rf₂.get .x5 = l0 := by
      rw [hrf₂, clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hx5]
    rw [hrf, clz_mvli_get_x14, hx5₂] at hn0
    have hsel : clzSelectedLimb l0 l1 l2 l3 = 0 := by
      unfold clzSelectedLimb
      rw [if_neg (by simp [hn3]), if_neg (by simp [hn2]),
        if_neg (by simp [hn1]), if_neg (by simp [hn0])]
    have hacc : clzSelectedAcc l0 l1 l2 l3 = 193 := by
      unfold clzSelectedAcc
      rw [if_neg (by simp [hn3]), if_neg (by simp [hn2]),
        if_neg (by simp [hn1]), if_neg (by simp [hn0])]
    subst hrf
    rw [clz_li_engine]
    unfold clzSelected
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx10
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx11
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx12
    · rw [RegFile.get_set_ne _ _ _ _ (by decide),
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₂,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide), hrf₁,
        clz_mvli_get_pres _ _ _ _ (by decide) (by decide)]
      exact hx13
    · rw [RegFile.get_set_ne _ _ _ _ (by decide), clz_mvli_get_x14, hx5₂,
        hsel]
      exact hn0
    · rw [RegFile.get_set_self _ _ _ (by decide), hacc]
  case clz.computed =>
    refine Stmt.sp_block_split _ _ ?_
    rintro rf ws A - hsel
    have hP := Stmt.sp_of_endsWith _ _
      (P := clzSelected p pc aux1 aux3 l0 l1 l2 l3)
      (by simp [clzSelectBody, Stmt.EndsWith]) rf ws A hsel
    obtain ⟨hx10, hx11, hx12, hx13, hx14, hx15, hA⟩ := hP
    unfold clzComputed
    refine ⟨?_, ?_, ?_, ?_, ?_, hA⟩
    · rw [clz_narrow_engine_preserve_x10, hx10]
    · rw [clz_narrow_engine_preserve_x11, hx11]
    · rw [clz_narrow_engine_preserve_x12, hx12]
    · rw [clz_narrow_engine_preserve_x13, hx13]
    · rw [clz_narrow_engine_x15, hx14, hx15]
      rfl
  case clz.store.focus =>
    rintro rf ws A ⟨hsp, hcomp⟩ hApc hp hhp
    obtain ⟨hx10, hx11, hx12, hx13, hx15, hA⟩ := hcomp
    rw [hA] at hhp
    refine ⟨clzCellBytes l0 l1 l2 l3, ⌜RwRegion.wf ⟨p, 32⟩⌝,
      ⟨hx12, rfl, rfl⟩, ?_, pcFree_pure, ?_⟩
    · rw [hx12]
      xperm_hyp hhp
    · rw [hx12, length_clzCellBytes]
      exact ((sepConj_pure_left hp).mp hhp).1
  case clz.store.mem =>
    rintro rf ws A win rest - hreach ⟨hptr, rfl, rfl⟩ -
    exact clz_store_blockVCs _ rf l0 l1 l2 l3
  case clz.post =>
    intro rf ws A h
    have h' := Stmt.sp_cut _ _
      (.blockAt "store" .x12 (clzStoreR p l0 l1 l2 l3) clzStoreBlock)
      "computed" rf ws A h
    refine Stmt.sp_blockAt_split _ _ ?_ rf ws A h'
    rintro rf₀ ws₀ A₀ win rest - hcomp - ⟨hptr, rfl, rfl⟩
    obtain ⟨hx10, hx11, hx12, hx13, hx15, -⟩ := hcomp
    rw [clz_store_engine]
    refine ⟨hx10, hx11, hx12, hx13, ?_⟩
    rw [hx12, hx15, sepConj_comm']


end ClzSAsm

end EvmAsm.Codegen
