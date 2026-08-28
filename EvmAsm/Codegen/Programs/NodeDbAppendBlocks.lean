/-
  EvmAsm.Codegen.Programs.NodeDbAppendBlocks

  **The straight-line blocks of the guest routine `node_db_append`**
  (GH #12318, the callee-composition lane).

  This module holds everything about `node_db_append` that does NOT touch a
  callee: the ABI-frame decomposition of the emitted program, the
  byte-region / dword-cell algebra the record header is written through, the
  five `la` sites, and the nine straight-line segments between the two
  `jal`s.  The composition — the two cross-calls, the whole body, the
  whole-routine triple, its node-DB restatement and the non-vacuity
  witnesses — is in the sibling `NodeDbAppendSpec.lean`, which imports this.

  Split purely for the 1500-line Codegen/Programs file cap; the two halves
  are one namespace.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Evm64.MptAssertions
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.Tactics.XCancelStruct

-- ⚠️ Deliberately off, for the reason recorded in `AddressFromPubkeySpec.lean`:
-- keccak's scratch base `Zk3` is `private` in `HashBridgeKeccakTop`, and a bare
-- occurrence would otherwise be auto-bound as a fresh universally quantified
-- `Word`, silently turning a claim about the scratch arena into a claim about an
-- arbitrary region.
set_option autoImplicit false

namespace EvmAsm.Codegen.NodeDbAppendSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Evm64
open EvmAsm.Evm64.Terminating
open EvmAsm.Codegen.Proofs

open private Zk3 from EvmAsm.Codegen.Proofs.HashBridgeKeccakTop

/-! ### `PCFree` instances the `pcFree` tactic needs

    Declared here rather than at the definitions because the frame
    assertions of this proof mix byte regions, register-list ownership and
    ABI frame slots; without them `pcFree` stops at the first such atom. -/

instance instPCFreeBytesRegionNda (b : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion b bs) := ⟨bytesRegion_pcFree _ _⟩

instance instPCFreeRegsAtNda (frame : FrameDesc) (vals : Reg → Word) :
    Assertion.PCFree (regsAt frame vals) := ⟨pcFree_regsAt _ _⟩

instance instPCFreeRegsOwnAtNda (frame : FrameDesc) :
    Assertion.PCFree (regsOwnAt frame) := ⟨pcFree_regsOwnAt _⟩

instance instPCFreeFrameSlotsOwnNda (frame : FrameDesc) (sp : Word) :
    Assertion.PCFree (frameSlotsOwn frame sp) := ⟨pcFree_frameSlotsOwn _ _⟩

instance instPCFreeFrameSlotsSavedNda (frame : FrameDesc) (sp : Word)
    (vals : Reg → Word) :
    Assertion.PCFree (frameSlotsSaved frame sp vals) := ⟨pcFree_frameSlotsSaved _ _ _⟩

instance instPCFreeRegOwnsNda (rs : List Reg) :
    Assertion.PCFree (regOwns rs) := ⟨pcFree_regOwns _⟩

/-- `pcf_r` — the `pcFree` closer extended with the byte-region / frame /
    register-list atoms this proof's caller frames are built from, and with
    `assumption` for the ambient `R.pcFree` hypothesis at the tail of every
    such chain. -/
macro "pcf_r" : tactic =>
  `(tactic| repeat (first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_regOwn
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regOwns _
      | exact pcFree_regsAt _ _
      | exact pcFree_regsOwnAt _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_nodeDbIs
      | assumption))

/-! ## §1  The linked routine, and its ABI-frame decomposition -/

/-- The routine's own guest address.  Nothing below is base-generic: the
    `la` immediates and the two `jal` displacements are baked against this
    pc. -/
def ndaB : Word := (GuestAddrs.node_db_append : Word)

/-- `zkvm_keccak256`'s linked entry. -/
def ndaK : Word := (GuestAddrs.zkvm_keccak256 : Word)

/-- The `.data` cells the routine touches. -/
def ndaHashLoc : Word := (GuestAddrs.mset_db_hash : Word)
def ndaTopLoc : Word := (GuestAddrs.mset_db_top : Word)
def ndaCntLoc : Word := (GuestAddrs.mset_db_count : Word)

/-- `node_db_append`'s saved-register frame: `ra`, `s0`, `s1`, `s2` in a
    32-byte frame.  `s0`/`s1` hold the node pointer and length across BOTH
    calls; `s2` holds the record cursor across the `mset_memcpy` call. -/
def ndaFrame : FrameDesc :=
  [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12)),
   (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12))]

/-- The body of `node_db_append`: instructions 5..41, everything between the
    frame prologue and the frame epilogue. -/
def ndaBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (Codegen.laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36)),
    .ADDI .x12 .x12 (Codegen.laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36)),
    .JAL .x1 (Codegen.jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.node_db_append + 44)),
    .AUIPC .x5 (Codegen.laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48)),
    .ADDI .x5 .x5 (Codegen.laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x6 (Codegen.laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60)),
    .ADDI .x6 .x6 (Codegen.laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60)),
    .LD .x7 .x6 (0 : BitVec 12),
    .SD .x18 .x7 (0 : BitVec 12),
    .LD .x7 .x6 (8 : BitVec 12),
    .SD .x18 .x7 (8 : BitVec 12),
    .LD .x7 .x6 (16 : BitVec 12),
    .SD .x18 .x7 (16 : BitVec 12),
    .LD .x7 .x6 (24 : BitVec 12),
    .SD .x18 .x7 (24 : BitVec 12),
    .SD .x18 .x9 (32 : BitVec 12),
    .ADDI .x10 .x18 (40 : BitVec 12),
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (Codegen.jalOff GuestAddrs.mset_memcpy (GuestAddrs.node_db_append + 116)),
    .ADDI .x5 .x9 (7 : BitVec 12),
    .ANDI .x5 .x5 (-8 : BitVec 12),
    .ADDI .x5 .x5 (40 : BitVec 12),
    .ADD .x18 .x18 .x5,
    .AUIPC .x6 (Codegen.laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136)),
    .ADDI .x6 .x6 (Codegen.laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136)),
    .SD .x6 .x18 (0 : BitVec 12),
    .AUIPC .x6 (Codegen.laHi GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148)),
    .ADDI .x6 .x6 (Codegen.laLo GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148)),
    .LD .x7 .x6 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .SD .x6 .x7 (0 : BitVec 12) ]

/-- **The frame decomposition**, kernel-checked by `rfl`: the emitted
    `nodeDbAppend_prog` IS the standard ABI frame around `ndaBody`.  If the
    emitted routine drifts (frame size, saved-register set, reordered
    prologue) this stops compiling. -/
theorem nodeDbAppend_prog_eq_abiFrame :
    nodeDbAppend_prog = abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) ndaFrame ndaBody :=
  rfl

theorem ndaBody_length : ndaBody.length = 37 := by decide

theorem ndaFrame_length : ndaFrame.length = 4 := by decide

/-- Total program length re-derived through the decomposition
    (`1 + 4 + 37 + 4 + 1 + 1 = 48`), agreeing with the `#guard` on
    `nodeDbAppend_prog` in `Programs/MptSetAcc.lean`. -/
theorem nodeDbAppend_prog_length : nodeDbAppend_prog.length = 48 := by decide

theorem ndaFrame_cons :
    ndaFrame = (.x1, (0 : BitVec 12)) ::
      [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12))] := rfl

theorem ndaFrame_ne_zero : ∀ p ∈ ndaFrame, p.1 ≠ .x0 := by decide

theorem ndaFrame_restore (sp0 : Word) :
    (sp0 + signExtend12 (-32 : BitVec 12)) + signExtend12 (32 : BitVec 12) = sp0 := by
  have h : signExtend12 (-32 : BitVec 12) + signExtend12 (32 : BitVec 12) = (0 : Word) := by
    decide
  rw [BitVec.add_assoc, h]
  simp

/-! ## §2  Instruction addressing -/

/-- Address of program instruction `k`. -/
def ndaAt (k : Nat) : Word := ndaB + BitVec.ofNat 64 (4 * k)

/-- The routine's own image `CodeReq` — the `guestImageEntries` pairing
    `(GuestAddrs.node_db_append, nodeDbAppend_prog)`. -/
def ndaCr : CodeReq := CodeReq.ofProg ndaB nodeDbAppend_prog

theorem ndaOfNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

theorem ndaAt_add (k j : Nat) :
    ndaAt k + BitVec.ofNat 64 (4 * j) = ndaAt (k + j) := by
  unfold ndaAt
  rw [BitVec.add_assoc, ndaOfNat_add]
  congr 2
  omega

theorem ndaAt_succ (k : Nat) : ndaAt k + 4 = ndaAt (k + 1) := by
  have h := ndaAt_add k 1
  rwa [show BitVec.ofNat 64 (4 * 1) = (4 : Word) from rfl] at h

/-- Instruction `k` of the routine is fetchable from the routine's own
    `CodeReq`. -/
theorem ndaMem (k : Nat) (instr : Instr)
    (hk : k < nodeDbAppend_prog.length)
    (hget : nodeDbAppend_prog.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton (ndaAt k) instr a = some i → ndaCr a = some i := by
  have m := CodeReq.ofProg_lookup_addr ndaB nodeDbAppend_prog k (ndaAt k)
    hk (by decide) rfl
  rw [hget] at m
  exact CodeReq.singleton_mono m

/-! ## §3  The three-image `CodeReq` -/

abbrev ndaKeccakCode : CodeReq := CodeReq.ofProg ndaK zkvmKeccak256_prog
abbrev ndaMemcpyCode : CodeReq :=
  CodeReq.ofProg msetMemcpyBase Codegen.msetMemcpy_prog
abbrev ndaCalleeCode : CodeReq := ndaKeccakCode.union ndaMemcpyCode
abbrev ndaFullCode : CodeReq := ndaCr.union ndaCalleeCode

theorem nda_wrapper_mem : ∀ a i, ndaCr a = some i → ndaFullCode a = some i :=
  fun a i h => CodeReq.union_mono_left a i h

private theorem nda_disj_wrapper_callees : ndaCr.Disjoint ndaCalleeCode := by
  refine CodeReq.Disjoint.union_right ?_ ?_
  · exact CodeReq.Disjoint.ofProg_ranges ndaB ndaK nodeDbAppend_prog
      zkvmKeccak256_prog
      (by rw [nodeDbAppend_prog_length]; decide) (by decide)
      (by rw [nodeDbAppend_prog_length]; decide)
  · exact CodeReq.Disjoint.ofProg_ranges ndaB msetMemcpyBase nodeDbAppend_prog
      Codegen.msetMemcpy_prog
      (by rw [nodeDbAppend_prog_length]; decide) (by decide)
      (by rw [nodeDbAppend_prog_length]; decide)

theorem nda_callee_mem : ∀ a i, ndaCalleeCode a = some i → ndaFullCode a = some i := by
  intro a i h
  exact CodeReq.mono_union_right nda_disj_wrapper_callees (fun _ _ h' => h') a i h

theorem nda_keccak_mem : ∀ a i, ndaKeccakCode a = some i → ndaFullCode a = some i :=
  fun a i h => nda_callee_mem a i (CodeReq.union_mono_left a i h)

private theorem nda_disj_keccak_memcpy : ndaKeccakCode.Disjoint ndaMemcpyCode :=
  CodeReq.Disjoint.ofProg_ranges ndaK msetMemcpyBase zkvmKeccak256_prog
    Codegen.msetMemcpy_prog (by decide) (by decide) (by decide)

theorem nda_memcpy_mem : ∀ a i, ndaMemcpyCode a = some i → ndaFullCode a = some i := by
  intro a i h
  exact nda_callee_mem a i
    (CodeReq.mono_union_right nda_disj_keccak_memcpy (fun _ _ h' => h') a i h)

/-- Instruction `k` of the routine, fetchable from the three-image union. -/
theorem ndaMemFull (k : Nat) (instr : Instr)
    (hk : k < nodeDbAppend_prog.length)
    (hget : nodeDbAppend_prog.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton (ndaAt k) instr a = some i → ndaFullCode a = some i :=
  fun a i h => nda_wrapper_mem a i (ndaMem k instr hk hget a i h)

/-! ## §4  Pure lemmas

    Byte-region ↔ dword-cell algebra (the routine moves the digest and the
    length through registers, so the record's first 40 bytes are five dword
    cells while they are being written), the record-log arithmetic, and the
    content model of the payload copy. -/

/-- The record log grows by one stride when a node is appended. -/
theorem nodeDbSize_snoc (xs : List (List (BitVec 8))) (n : List (BitVec 8)) :
    nodeDbSize (xs ++ [n]) = nodeDbSize xs + nodeDbStride n := by
  induction xs with
  | nil => simp [nodeDbSize, nodeDbStride]
  | cons a rest ih =>
    rw [List.cons_append, nodeDbSize_cons, ih, nodeDbSize_cons]
    omega

/-- **The payload copy's content model.**  `mset_memcpy` overwrites the first
    `n` bytes of the destination with the whole source; everything past `n`
    is the destination's original bytes — which is how the zero pad of the
    record survives. -/
theorem copyIntoRegion_prefix (dst src : List (BitVec 8))
    (hd : src.length ≤ dst.length) :
    copyIntoRegion dst src 0 0 src.length = src ++ dst.drop src.length := by
  refine List.ext_getElem (by
    rw [copyIntoRegion_length, List.length_append, List.length_drop]
    omega) ?_
  intro j h1 h2
  rw [copyIntoRegion_length] at h1
  rw [copyIntoRegion_getElem dst src 0 0 src.length j h1]
  by_cases hj : j < src.length
  · rw [if_pos ⟨Nat.zero_le _, by omega⟩, Nat.sub_zero, Nat.zero_add,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      List.getElem_append_left hj]
    rfl
  · rw [if_neg (by omega)]
    rw [List.getElem_append_right (by omega), List.getElem_drop]
    congr 1
    omega

/-- A single-dword region is one memory cell. -/
theorem bytesRegion_dword_cell (b v : Word) :
    bytesRegion b (dwordBytes v) = ((b ↦ₘ v) ** empAssertion) := by
  rw [bytesRegion_eq_cons b (dwordBytes v) (by simp [dwordBytes]),
    List.take_of_length_le (by rw [length_dwordBytes]),
    packBytes_dwordBytes,
    List.drop_eq_nil_of_le (by rw [length_dwordBytes]),
    bytesRegion_nil]

/-- One `bytesRegion` peel, as an equation on assertions. -/
private theorem region_step (b : Word) (bs : List (BitVec 8)) (h : bs ≠ []) :
    bytesRegion b bs = ((b ↦ₘ packBytes (bs.take 8)) ** bytesRegion (b + 8) (bs.drop 8)) :=
  bytesRegion_eq_cons b bs h

private theorem drop_ne_nil {bs : List (BitVec 8)} {k n : Nat}
    (h : bs.length = n) (hk : k < n) : bs.drop k ≠ [] := by
  intro hc
  have hl := congrArg List.length hc
  simp only [List.length_drop, List.length_nil, h] at hl
  omega

/-- **A 40-byte region is five dword cells.**  The record header the routine
    writes (`hash[32] | len:u64`) is exactly this window. -/
theorem region40_split (b : Word) (bs : List (BitVec 8)) (h : bs.length = 40) :
    bytesRegion b bs =
      ((b ↦ₘ packBytes (bs.take 8)) **
       ((b + 8) ↦ₘ packBytes ((bs.drop 8).take 8)) **
       ((b + 16) ↦ₘ packBytes ((bs.drop 16).take 8)) **
       ((b + 24) ↦ₘ packBytes ((bs.drop 24).take 8)) **
       ((b + 32) ↦ₘ packBytes ((bs.drop 32).take 8))) := by
  have h1 : bs ≠ [] := by intro hc; rw [hc] at h; simp at h
  have h8 : bs.drop 8 ≠ [] := drop_ne_nil h (by omega)
  have h16 : bs.drop 16 ≠ [] := drop_ne_nil h (by omega)
  have h24 : bs.drop 24 ≠ [] := drop_ne_nil h (by omega)
  have h32 : bs.drop 32 ≠ [] := drop_ne_nil h (by omega)
  have d16 : (bs.drop 8).drop 8 = bs.drop 16 := by simp [List.drop_drop]
  have d24 : (bs.drop 16).drop 8 = bs.drop 24 := by simp [List.drop_drop]
  have d32 : (bs.drop 24).drop 8 = bs.drop 32 := by simp [List.drop_drop]
  have d40 : (bs.drop 32).drop 8 = [] := by
    rw [List.drop_drop]
    exact List.drop_eq_nil_of_le (by omega)
  rw [region_step b bs h1, region_step (b + 8) (bs.drop 8) h8, d16]
  rw [show (b + 8 + 8 : Word) = b + 16 from by bv_omega]
  rw [region_step (b + 16) (bs.drop 16) h16, d24]
  rw [show (b + 16 + 8 : Word) = b + 24 from by bv_omega]
  rw [region_step (b + 24) (bs.drop 24) h24, d32]
  rw [show (b + 24 + 8 : Word) = b + 32 from by bv_omega]
  rw [region_step (b + 32) (bs.drop 32) h32, d40, bytesRegion_nil]
  simp only [sepConj_emp_right']

/-- **A 32-byte region is four dword cells** — the `mset_db_hash` digest
    buffer, which the routine reads out one dword at a time. -/
theorem region32_split (b : Word) (bs : List (BitVec 8)) (h : bs.length = 32) :
    bytesRegion b bs =
      ((b ↦ₘ packBytes (bs.take 8)) **
       ((b + 8) ↦ₘ packBytes ((bs.drop 8).take 8)) **
       ((b + 16) ↦ₘ packBytes ((bs.drop 16).take 8)) **
       ((b + 24) ↦ₘ packBytes ((bs.drop 24).take 8))) := by
  have h1 : bs ≠ [] := by intro hc; rw [hc] at h; simp at h
  have h8 : bs.drop 8 ≠ [] := drop_ne_nil h (by omega)
  have h16 : bs.drop 16 ≠ [] := drop_ne_nil h (by omega)
  have h24 : bs.drop 24 ≠ [] := drop_ne_nil h (by omega)
  have d16 : (bs.drop 8).drop 8 = bs.drop 16 := by simp [List.drop_drop]
  have d24 : (bs.drop 16).drop 8 = bs.drop 24 := by simp [List.drop_drop]
  have d32 : (bs.drop 24).drop 8 = [] := by
    rw [List.drop_drop]
    exact List.drop_eq_nil_of_le (by omega)
  rw [region_step b bs h1, region_step (b + 8) (bs.drop 8) h8, d16]
  rw [show (b + 8 + 8 : Word) = b + 16 from by bv_omega]
  rw [region_step (b + 16) (bs.drop 16) h16, d24]
  rw [show (b + 16 + 8 : Word) = b + 24 from by bv_omega]
  rw [region_step (b + 24) (bs.drop 24) h24, d32, bytesRegion_nil]
  simp only [sepConj_emp_right']

/-- **Five dword cells are a 40-byte region** — the join direction, used on
    the record header once the five stores have landed. -/
theorem region40_join (b : Word) (w0 w1 w2 w3 w4 : Word) :
    ((b ↦ₘ w0) ** ((b + 8) ↦ₘ w1) ** ((b + 16) ↦ₘ w2) **
      ((b + 24) ↦ₘ w3) ** ((b + 32) ↦ₘ w4))
      = bytesRegion b (dwordBytes w0 ++ dwordBytes w1 ++ dwordBytes w2 ++
          dwordBytes w3 ++ dwordBytes w4) := by
  have hlen : ∀ w : Word, (dwordBytes w).length = 8 := fun w => length_dwordBytes w
  have hd : ∀ w : Word, (8 : Nat) ∣ (dwordBytes w).length := by
    intro w; rw [hlen w]
  have hd2 : ∀ w w' : Word, (8 : Nat) ∣ (dwordBytes w ++ dwordBytes w').length := by
    intro w w'; rw [List.length_append, hlen w, hlen w']; exact ⟨2, rfl⟩
  have hd3 : ∀ w w' w'' : Word,
      (8 : Nat) ∣ (dwordBytes w ++ dwordBytes w' ++ dwordBytes w'').length := by
    intro w w' w''
    rw [List.length_append, List.length_append, hlen w, hlen w', hlen w'']
    exact ⟨3, rfl⟩
  have hd4 : ∀ w w' w'' w''' : Word,
      (8 : Nat) ∣ (dwordBytes w ++ dwordBytes w' ++ dwordBytes w'' ++
        dwordBytes w''').length := by
    intro w w' w'' w'''
    rw [List.length_append, List.length_append, List.length_append,
      hlen w, hlen w', hlen w'', hlen w''']
    exact ⟨4, rfl⟩
  rw [bytesRegion_append b _ (dwordBytes w4) (hd4 w0 w1 w2 w3),
    bytesRegion_append b _ (dwordBytes w3) (hd3 w0 w1 w2),
    bytesRegion_append b _ (dwordBytes w2) (hd2 w0 w1),
    bytesRegion_append b _ (dwordBytes w1) (hd w0)]
  rw [bytesRegion_dword_cell b w0, bytesRegion_dword_cell _ w1,
    bytesRegion_dword_cell _ w2, bytesRegion_dword_cell _ w3,
    bytesRegion_dword_cell _ w4]
  rw [show (dwordBytes w0).length = 8 from hlen w0,
    show (dwordBytes w0 ++ dwordBytes w1).length = 16 from by
      rw [List.length_append, hlen w0, hlen w1],
    show (dwordBytes w0 ++ dwordBytes w1 ++ dwordBytes w2).length = 24 from by
      rw [List.length_append, List.length_append, hlen w0, hlen w1, hlen w2],
    show (dwordBytes w0 ++ dwordBytes w1 ++ dwordBytes w2 ++
        dwordBytes w3).length = 32 from by
      rw [List.length_append, List.length_append, List.length_append,
        hlen w0, hlen w1, hlen w2, hlen w3]]
  rw [show (BitVec.ofNat 64 8 : Word) = 8 from rfl,
    show (BitVec.ofNat 64 16 : Word) = 16 from rfl,
    show (BitVec.ofNat 64 24 : Word) = 24 from rfl,
    show (BitVec.ofNat 64 32 : Word) = 32 from rfl]
  simp only [sepConj_emp_right', sepConj_assoc']

/-- A 32-byte list is its four dword chunks, concatenated. -/
theorem take_drop_32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    bs.take 8 ++ (bs.drop 8).take 8 ++ (bs.drop 16).take 8 ++ (bs.drop 24).take 8 = bs := by
  have d16 : (bs.drop 8).drop 8 = bs.drop 16 := by simp [List.drop_drop]
  have d24 : (bs.drop 16).drop 8 = bs.drop 24 := by simp [List.drop_drop]
  have d32 : (bs.drop 24).drop 8 = [] := by
    rw [List.drop_drop]
    exact List.drop_eq_nil_of_le (by omega)
  have e3 : (bs.drop 24).take 8 = bs.drop 24 := by
    have := List.take_append_drop 8 (bs.drop 24)
    rw [d32, List.append_nil] at this
    exact this
  have e2 : (bs.drop 16).take 8 ++ bs.drop 24 = bs.drop 16 := by
    have := List.take_append_drop 8 (bs.drop 16)
    rwa [d24] at this
  have e1 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
    have := List.take_append_drop 8 (bs.drop 8)
    rwa [d16] at this
  have e0 : bs.take 8 ++ bs.drop 8 = bs := List.take_append_drop 8 bs
  calc bs.take 8 ++ (bs.drop 8).take 8 ++ (bs.drop 16).take 8 ++ (bs.drop 24).take 8
      = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ (bs.drop 24).take 8)) := by
        simp [List.append_assoc]
    _ = bs := by rw [e3, e2, e1, e0]

/-- The record's bytes split at the 40-byte header boundary — the seam the
    routine writes on either side of (five dword stores, then a
    `mset_memcpy`). -/
theorem nodeDbRecordBytes_split (node : List (BitVec 8)) :
    nodeDbRecordBytes node =
      (Stateless.SpecRef.keccak256 node ++
        Stateless.SpecRef.natToBytesLE 8 node.length) ++
      (node ++ List.replicate (roundUp8 node.length - node.length) 0) := by
  simp only [nodeDbRecordBytes, List.append_assoc]

/-! ## §5  Immediate-sign-extension constants -/

private theorem se0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se7 : signExtend12 (7 : BitVec 12) = (7 : Word) := by decide
private theorem se8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem se24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
private theorem se32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
private theorem se40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
private theorem seNeg8 : signExtend12 (-8 : BitVec 12) = ~~~(7 : Word) := by decide

theorem add_zero_word (w : Word) : w + (0 : Word) = w := by bv_omega

/-! ## §6  The `la` segment, proven once

    Five `auipc`/`addi` pairs materialise three `.data` addresses.  Each is
    the same two-instruction shape, so `la_materialize_within` is wrapped
    once with a caller frame and instantiated five times. -/

theorem la_seg_spec (pc : Word) (rd : Reg) (target vOld : Word) (cr : CodeReq)
    (hi : BitVec 20) (lo : BitVec 12)
    (hrd : rd ≠ .x0)
    (hhi : hi = Rv64.laHi pc target) (hlo : lo = Rv64.laLo pc target)
    (hrange : laInRange pc target)
    (hau : ∀ a i, CodeReq.singleton pc (.AUIPC rd hi) a = some i → cr a = some i)
    (had : ∀ a i, CodeReq.singleton (pc + 4) (.ADDI rd rd lo) a = some i → cr a = some i)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 2 pc (pc + 8) cr ((rd ↦ᵣ vOld) ** R) ((rd ↦ᵣ target) ** R) := by
  subst hhi
  subst hlo
  exact cpsTripleWithin_frameR R hR
    (la_materialize_within rd vOld pc target hrd hrange hau had)

/-! ### The five `la` sites, bridged from the emitter's immediates -/

private theorem ndaAt_9 : ndaAt 9 = ndaB + 36 := by unfold ndaAt; rfl
private theorem ndaAt_12 : ndaAt 12 = ndaB + 48 := by unfold ndaAt; rfl
private theorem ndaAt_15 : ndaAt 15 = ndaB + 60 := by unfold ndaAt; rfl
private theorem ndaAt_34 : ndaAt 34 = ndaB + 136 := by unfold ndaAt; rfl
private theorem ndaAt_37 : ndaAt 37 = ndaB + 148 := by unfold ndaAt; rfl

private theorem la9_hi :
    Codegen.laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36)
      = Rv64.laHi (ndaAt 9) ndaHashLoc := by
  rw [ndaAt_9]; decide
private theorem la9_lo :
    Codegen.laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36)
      = Rv64.laLo (ndaAt 9) ndaHashLoc := by
  rw [ndaAt_9]; decide
private theorem la9_range : laInRange (ndaAt 9) ndaHashLoc := by
  rw [ndaAt_9]; decide

private theorem la12_hi :
    Codegen.laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48)
      = Rv64.laHi (ndaAt 12) ndaTopLoc := by
  rw [ndaAt_12]; decide
private theorem la12_lo :
    Codegen.laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48)
      = Rv64.laLo (ndaAt 12) ndaTopLoc := by
  rw [ndaAt_12]; decide
private theorem la12_range : laInRange (ndaAt 12) ndaTopLoc := by
  rw [ndaAt_12]; decide

private theorem la15_hi :
    Codegen.laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60)
      = Rv64.laHi (ndaAt 15) ndaHashLoc := by
  rw [ndaAt_15]; decide
private theorem la15_lo :
    Codegen.laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60)
      = Rv64.laLo (ndaAt 15) ndaHashLoc := by
  rw [ndaAt_15]; decide
private theorem la15_range : laInRange (ndaAt 15) ndaHashLoc := by
  rw [ndaAt_15]; decide

private theorem la34_hi :
    Codegen.laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136)
      = Rv64.laHi (ndaAt 34) ndaTopLoc := by
  rw [ndaAt_34]; decide
private theorem la34_lo :
    Codegen.laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136)
      = Rv64.laLo (ndaAt 34) ndaTopLoc := by
  rw [ndaAt_34]; decide
private theorem la34_range : laInRange (ndaAt 34) ndaTopLoc := by
  rw [ndaAt_34]; decide

private theorem la37_hi :
    Codegen.laHi GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148)
      = Rv64.laHi (ndaAt 37) ndaCntLoc := by
  rw [ndaAt_37]; decide
private theorem la37_lo :
    Codegen.laLo GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148)
      = Rv64.laLo (ndaAt 37) ndaCntLoc := by
  rw [ndaAt_37]; decide
private theorem la37_range : laInRange (ndaAt 37) ndaCntLoc := by
  rw [ndaAt_37]; decide

/-! ## §7  The straight-line segments

    Nine segments, split at the two `jal`s and at the points where the
    register footprint changes.  Each is stated over the routine's OWN
    `CodeReq` (`ndaCr`) with a generic caller frame `R`; the call legs widen
    to the three-image union. -/

/-- **Indices 5-10: keccak's three arguments.**  `s0`/`s1` park the node
    pointer and its length (they must survive the call), `a0`/`a1` are
    re-loaded from them, and the `la` pair puts `&mset_db_hash` in `a2`. -/
theorem nda_setup_spec (nodePtr lenW v8 v9 v12 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 6 (ndaAt 5) (ndaAt 11) ndaCr
      (((.x10 : Reg) ↦ᵣ nodePtr) ** ((.x11 : Reg) ↦ᵣ lenW) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x12 : Reg) ↦ᵣ v12) ** R)
      (((.x10 : Reg) ↦ᵣ nodePtr) ** ((.x11 : Reg) ↦ᵣ lenW) **
        ((.x8 : Reg) ↦ᵣ nodePtr) ** ((.x9 : Reg) ↦ᵣ lenW) **
        ((.x12 : Reg) ↦ᵣ ndaHashLoc) ** R) := by
  have s5 := cpsTripleWithin_extend_code (ndaMem 5 (.MV .x8 .x10) (by decide) rfl)
    (mv_spec_gen_within .x8 .x10 nodePtr v8 (ndaAt 5) (by decide))
  rw [ndaAt_succ 5] at s5
  have f5 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ lenW) ** ((.x9 : Reg) ↦ᵣ v9) ** ((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcf_r) s5
  have s6 := cpsTripleWithin_extend_code (ndaMem 6 (.MV .x9 .x11) (by decide) rfl)
    (mv_spec_gen_within .x9 .x11 lenW v9 (ndaAt 6) (by decide))
  rw [ndaAt_succ 6] at s6
  have f6 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ nodePtr) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
      ((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcf_r) s6
  have s7 := cpsTripleWithin_extend_code (ndaMem 7 (.MV .x10 .x8) (by decide) rfl)
    (mv_spec_gen_within .x10 .x8 nodePtr nodePtr (ndaAt 7) (by decide))
  rw [ndaAt_succ 7] at s7
  have f7 := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ lenW) ** ((.x9 : Reg) ↦ᵣ lenW) ** ((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcf_r) s7
  have s8 := cpsTripleWithin_extend_code (ndaMem 8 (.MV .x11 .x9) (by decide) rfl)
    (mv_spec_gen_within .x11 .x9 lenW lenW (ndaAt 8) (by decide))
  rw [ndaAt_succ 8] at s8
  have f8 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ nodePtr) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
      ((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcf_r) s8
  have hla := la_seg_spec (ndaAt 9) .x12 ndaHashLoc v12 ndaCr
    (Codegen.laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36))
    (Codegen.laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 36))
    (by decide) la9_hi la9_lo la9_range
    (ndaMem 9 _ (by decide) rfl)
    (by
      rw [ndaAt_succ 9]
      exact ndaMem 10 _ (by decide) rfl)
    (((.x10 : Reg) ↦ᵣ nodePtr) ** ((.x11 : Reg) ↦ᵣ lenW) **
      ((.x8 : Reg) ↦ᵣ nodePtr) ** ((.x9 : Reg) ↦ᵣ lenW) ** R)
    (by pcf_r)
  rw [show (ndaAt 9 + 8 : Word) = ndaAt 11 from by
    have h := ndaAt_add 9 2
    rwa [show BitVec.ofNat 64 (4 * 2) = (8 : Word) from rfl] at h] at hla
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f5 f6
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f7
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f8
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 hla
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c4

/-- **Indices 12-14: materialise `&mset_db_top` and read the bump pointer
    into `s2`.** -/
theorem nda_top_load_spec (topAddr v5 v18 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 3 (ndaAt 12) (ndaAt 15) ndaCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x18 : Reg) ↦ᵣ v18) **
        (ndaTopLoc ↦ₘ topAddr) ** R)
      (((.x5 : Reg) ↦ᵣ ndaTopLoc) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        (ndaTopLoc ↦ₘ topAddr) ** R) := by
  have hla := la_seg_spec (ndaAt 12) .x5 ndaTopLoc v5 ndaCr
    (Codegen.laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48))
    (Codegen.laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 48))
    (by decide) la12_hi la12_lo la12_range
    (ndaMem 12 _ (by decide) rfl)
    (by
      rw [ndaAt_succ 12]
      exact ndaMem 13 _ (by decide) rfl)
    (((.x18 : Reg) ↦ᵣ v18) ** (ndaTopLoc ↦ₘ topAddr) ** R)
    (by pcf_r)
  rw [show (ndaAt 12 + 8 : Word) = ndaAt 14 from by
    have h := ndaAt_add 12 2
    rwa [show BitVec.ofNat 64 (4 * 2) = (8 : Word) from rfl] at h] at hla
  have s14 := cpsTripleWithin_extend_code
    (ndaMem 14 (.LD .x18 .x5 (0 : BitVec 12)) (by decide) rfl)
    (ld_spec_gen_within .x18 .x5 ndaTopLoc v18 topAddr (0 : BitVec 12) (ndaAt 14)
      (by decide))
  rw [ndaAt_succ 14, se0, add_zero_word] at s14
  have f14 := cpsTripleWithin_frameR R hR s14
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) hla f14
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c1

/-- **Indices 15-16: materialise `&mset_db_hash` in `t1`.** -/
theorem nda_hash_la_spec (v6 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 2 (ndaAt 15) (ndaAt 17) ndaCr
      (((.x6 : Reg) ↦ᵣ v6) ** R)
      (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** R) := by
  have hla := la_seg_spec (ndaAt 15) .x6 ndaHashLoc v6 ndaCr
    (Codegen.laHi GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60))
    (Codegen.laLo GuestAddrs.mset_db_hash (GuestAddrs.node_db_append + 60))
    (by decide) la15_hi la15_lo la15_range
    (ndaMem 15 _ (by decide) rfl)
    (by
      rw [ndaAt_succ 15]
      exact ndaMem 16 _ (by decide) rfl)
    R hR
  rwa [show (ndaAt 15 + 8 : Word) = ndaAt 17 from by
    have h := ndaAt_add 15 2
    rwa [show BitVec.ofNat 64 (4 * 2) = (8 : Word) from rfl] at h] at hla

/-- **Indices 17-24: the four-dword digest copy.**  `ld t2, 8q(t1)` /
    `sd t2, 8q(s2)` moves the 32-byte keccak digest from `mset_db_hash` into
    the record's hash field, one dword at a time.  The source cells are
    read-only; the four destination cells end up holding the source values,
    which is what makes the record's first 32 bytes the digest. -/
theorem nda_hash_copy_spec (topAddr v7 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 8 (ndaAt 17) (ndaAt 25) ndaCr
      (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        ((.x7 : Reg) ↦ᵣ v7) **
        (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
        ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
        (topAddr ↦ₘ e0) ** ((topAddr + 8) ↦ₘ e1) **
        ((topAddr + 16) ↦ₘ e2) ** ((topAddr + 24) ↦ₘ e3) ** R)
      (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        ((.x7 : Reg) ↦ᵣ d3) **
        (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
        ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
        (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) **
        ((topAddr + 16) ↦ₘ d2) ** ((topAddr + 24) ↦ₘ d3) ** R) := by
  -- 17: ld t2, 0(t1)
  have s17 := cpsTripleWithin_extend_code
    (ndaMem 17 (.LD .x7 .x6 (0 : BitVec 12)) (by decide) rfl)
    (ld_spec_gen_within .x7 .x6 ndaHashLoc v7 d0 (0 : BitVec 12) (ndaAt 17) (by decide))
  rw [ndaAt_succ 17, se0, add_zero_word] at s17
  -- 18: sd t2, 0(s2)
  have s18 := cpsTripleWithin_extend_code
    (ndaMem 18 (.SD .x18 .x7 (0 : BitVec 12)) (by decide) rfl)
    (sd_spec_gen_within .x18 .x7 topAddr d0 e0 (0 : BitVec 12) (ndaAt 18))
  rw [ndaAt_succ 18, se0, add_zero_word] at s18
  -- 19/20
  have s19 := cpsTripleWithin_extend_code
    (ndaMem 19 (.LD .x7 .x6 (8 : BitVec 12)) (by decide) rfl)
    (ld_spec_gen_within .x7 .x6 ndaHashLoc d0 d1 (8 : BitVec 12) (ndaAt 19) (by decide))
  rw [ndaAt_succ 19, se8] at s19
  have s20 := cpsTripleWithin_extend_code
    (ndaMem 20 (.SD .x18 .x7 (8 : BitVec 12)) (by decide) rfl)
    (sd_spec_gen_within .x18 .x7 topAddr d1 e1 (8 : BitVec 12) (ndaAt 20))
  rw [ndaAt_succ 20, se8] at s20
  -- 21/22
  have s21 := cpsTripleWithin_extend_code
    (ndaMem 21 (.LD .x7 .x6 (16 : BitVec 12)) (by decide) rfl)
    (ld_spec_gen_within .x7 .x6 ndaHashLoc d1 d2 (16 : BitVec 12) (ndaAt 21) (by decide))
  rw [ndaAt_succ 21, se16] at s21
  have s22 := cpsTripleWithin_extend_code
    (ndaMem 22 (.SD .x18 .x7 (16 : BitVec 12)) (by decide) rfl)
    (sd_spec_gen_within .x18 .x7 topAddr d2 e2 (16 : BitVec 12) (ndaAt 22))
  rw [ndaAt_succ 22, se16] at s22
  -- 23/24
  have s23 := cpsTripleWithin_extend_code
    (ndaMem 23 (.LD .x7 .x6 (24 : BitVec 12)) (by decide) rfl)
    (ld_spec_gen_within .x7 .x6 ndaHashLoc d2 d3 (24 : BitVec 12) (ndaAt 23) (by decide))
  rw [ndaAt_succ 23, se24] at s23
  have s24 := cpsTripleWithin_extend_code
    (ndaMem 24 (.SD .x18 .x7 (24 : BitVec 12)) (by decide) rfl)
    (sd_spec_gen_within .x18 .x7 topAddr d3 e3 (24 : BitVec 12) (ndaAt 24))
  rw [ndaAt_succ 24, se24] at s24
  -- frames
  have f17 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ topAddr) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ e0) ** ((topAddr + 8) ↦ₘ e1) **
      ((topAddr + 16) ↦ₘ e2) ** ((topAddr + 24) ↦ₘ e3) ** R)
    (by pcf_r) s17
  have f18 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      ((topAddr + 8) ↦ₘ e1) ** ((topAddr + 16) ↦ₘ e2) ** ((topAddr + 24) ↦ₘ e3) ** R)
    (by pcf_r) s18
  have f19 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ topAddr) ** (ndaHashLoc ↦ₘ d0) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ e1) **
      ((topAddr + 16) ↦ₘ e2) ** ((topAddr + 24) ↦ₘ e3) ** R)
    (by pcf_r) s19
  have f20 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ d0) ** ((topAddr + 16) ↦ₘ e2) ** ((topAddr + 24) ↦ₘ e3) ** R)
    (by pcf_r) s20
  have f21 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ topAddr) ** (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) **
      ((topAddr + 16) ↦ₘ e2) ** ((topAddr + 24) ↦ₘ e3) ** R)
    (by pcf_r) s21
  have f22 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) ** ((topAddr + 24) ↦ₘ e3) ** R)
    (by pcf_r) s22
  have f23 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ topAddr) ** (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) **
      (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) **
      ((topAddr + 16) ↦ₘ d2) ** ((topAddr + 24) ↦ₘ e3) ** R)
    (by pcf_r) s23
  have f24 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) ** ((topAddr + 16) ↦ₘ d2) ** R)
    (by pcf_r) s24
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f17 f18
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f19
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f20
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 f21
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c4 f22
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c5 f23
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c6 f24
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c7

/-- **Index 25: the length field.**  `sd s1, 32(s2)` writes the node length
    as the record's little-endian u64 length word. -/
theorem nda_len_store_spec (topAddr lenW e4 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 1 (ndaAt 25) (ndaAt 26) ndaCr
      (((.x18 : Reg) ↦ᵣ topAddr) ** ((.x9 : Reg) ↦ᵣ lenW) **
        ((topAddr + 32) ↦ₘ e4) ** R)
      (((.x18 : Reg) ↦ᵣ topAddr) ** ((.x9 : Reg) ↦ᵣ lenW) **
        ((topAddr + 32) ↦ₘ lenW) ** R) := by
  have s25 := cpsTripleWithin_extend_code
    (ndaMem 25 (.SD .x18 .x9 (32 : BitVec 12)) (by decide) rfl)
    (sd_spec_gen_within .x18 .x9 topAddr lenW e4 (32 : BitVec 12) (ndaAt 25))
  rw [ndaAt_succ 25, se32] at s25
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) (cpsTripleWithin_frameR R hR s25)

/-- **Indices 26-28: `mset_memcpy`'s three arguments** — destination
    `record + 40`, source `s0`, count `s1`. -/
theorem nda_memcpy_args_spec (topAddr nodePtr lenW v10 v11 v12 : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 3 (ndaAt 26) (ndaAt 29) ndaCr
      (((.x18 : Reg) ↦ᵣ topAddr) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
        ((.x9 : Reg) ↦ᵣ lenW) ** ((.x10 : Reg) ↦ᵣ v10) **
        ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** R)
      (((.x18 : Reg) ↦ᵣ topAddr) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
        ((.x9 : Reg) ↦ᵣ lenW) ** ((.x10 : Reg) ↦ᵣ (topAddr + 40)) **
        ((.x11 : Reg) ↦ᵣ nodePtr) ** ((.x12 : Reg) ↦ᵣ lenW) ** R) := by
  have s26 := cpsTripleWithin_extend_code
    (ndaMem 26 (.ADDI .x10 .x18 (40 : BitVec 12)) (by decide) rfl)
    (addi_spec_gen_within .x10 .x18 v10 topAddr (40 : BitVec 12) (ndaAt 26) (by decide))
  rw [ndaAt_succ 26, se40] at s26
  have f26 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ nodePtr) ** ((.x9 : Reg) ↦ᵣ lenW) **
      ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcf_r) s26
  have s27 := cpsTripleWithin_extend_code
    (ndaMem 27 (.MV .x11 .x8) (by decide) rfl)
    (mv_spec_gen_within .x11 .x8 nodePtr v11 (ndaAt 27) (by decide))
  rw [ndaAt_succ 27] at s27
  have f27 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ topAddr) ** ((.x9 : Reg) ↦ᵣ lenW) **
      ((.x10 : Reg) ↦ᵣ (topAddr + 40)) ** ((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcf_r) s27
  have s28 := cpsTripleWithin_extend_code
    (ndaMem 28 (.MV .x12 .x9) (by decide) rfl)
    (mv_spec_gen_within .x12 .x9 lenW v12 (ndaAt 28) (by decide))
  rw [ndaAt_succ 28] at s28
  have f28 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ topAddr) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
      ((.x10 : Reg) ↦ᵣ (topAddr + 40)) ** ((.x11 : Reg) ↦ᵣ nodePtr) ** R)
    (by pcf_r) s28
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f26 f27
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f28
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c2

/-- The record stride the routine computes in `t0`:
    `((len + 7) &&& ~7) + 40`.  `roundUp8_eq_alignToDword` (MptAssertions)
    identifies the mask with `roundUp8`. -/
def ndaStrideWord (lenW : Word) : Word := ((lenW + (7 : Word)) &&& ~~~(7 : Word)) + (40 : Word)

/-- **Indices 30-33: the bump-pointer arithmetic.** -/
theorem nda_bump_spec (topAddr lenW v5 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 4 (ndaAt 30) (ndaAt 34) ndaCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x9 : Reg) ↦ᵣ lenW) **
        ((.x18 : Reg) ↦ᵣ topAddr) ** R)
      (((.x5 : Reg) ↦ᵣ ndaStrideWord lenW) ** ((.x9 : Reg) ↦ᵣ lenW) **
        ((.x18 : Reg) ↦ᵣ (topAddr + ndaStrideWord lenW)) ** R) := by
  have s30 := cpsTripleWithin_extend_code
    (ndaMem 30 (.ADDI .x5 .x9 (7 : BitVec 12)) (by decide) rfl)
    (addi_spec_gen_within .x5 .x9 v5 lenW (7 : BitVec 12) (ndaAt 30) (by decide))
  rw [ndaAt_succ 30, se7] at s30
  have f30 := cpsTripleWithin_frameR (((.x18 : Reg) ↦ᵣ topAddr) ** R)
    (by pcf_r) s30
  have s31 := cpsTripleWithin_extend_code
    (ndaMem 31 (.ANDI .x5 .x5 (-8 : BitVec 12)) (by decide) rfl)
    (andi_spec_gen_same_within .x5 (lenW + (7 : Word)) (-8 : BitVec 12) (ndaAt 31)
      (by decide))
  rw [ndaAt_succ 31, seNeg8] at s31
  have f31 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ topAddr) ** R)
    (by pcf_r) s31
  have s32 := cpsTripleWithin_extend_code
    (ndaMem 32 (.ADDI .x5 .x5 (40 : BitVec 12)) (by decide) rfl)
    (addi_spec_gen_same_within .x5 ((lenW + (7 : Word)) &&& ~~~(7 : Word))
      (40 : BitVec 12) (ndaAt 32) (by decide))
  rw [ndaAt_succ 32, se40] at s32
  have f32 := cpsTripleWithin_frameR
    (((.x9 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ topAddr) ** R)
    (by pcf_r) s32
  have s33 := cpsTripleWithin_extend_code
    (ndaMem 33 (.ADD .x18 .x18 .x5) (by decide) rfl)
    (add_spec_rd_eq_rs1_within .x18 .x5 topAddr (ndaStrideWord lenW) (ndaAt 33)
      (by decide))
  rw [ndaAt_succ 33] at s33
  have f33 := cpsTripleWithin_frameR (((.x9 : Reg) ↦ᵣ lenW) ** R)
    (by pcf_r) s33
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f30 f31
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f32
  rw [show ((lenW + (7 : Word)) &&& ~~~(7 : Word)) + (40 : Word) = ndaStrideWord lenW
      from rfl] at c2
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f33
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c3

/-- **Indices 34-36: publish the new bump pointer.** -/
theorem nda_top_store_spec (newTop oldTop v6 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 3 (ndaAt 34) (ndaAt 37) ndaCr
      (((.x6 : Reg) ↦ᵣ v6) ** ((.x18 : Reg) ↦ᵣ newTop) **
        (ndaTopLoc ↦ₘ oldTop) ** R)
      (((.x6 : Reg) ↦ᵣ ndaTopLoc) ** ((.x18 : Reg) ↦ᵣ newTop) **
        (ndaTopLoc ↦ₘ newTop) ** R) := by
  have hla := la_seg_spec (ndaAt 34) .x6 ndaTopLoc v6 ndaCr
    (Codegen.laHi GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136))
    (Codegen.laLo GuestAddrs.mset_db_top (GuestAddrs.node_db_append + 136))
    (by decide) la34_hi la34_lo la34_range
    (ndaMem 34 _ (by decide) rfl)
    (by
      rw [ndaAt_succ 34]
      exact ndaMem 35 _ (by decide) rfl)
    (((.x18 : Reg) ↦ᵣ newTop) ** (ndaTopLoc ↦ₘ oldTop) ** R)
    (by pcf_r)
  rw [show (ndaAt 34 + 8 : Word) = ndaAt 36 from by
    have h := ndaAt_add 34 2
    rwa [show BitVec.ofNat 64 (4 * 2) = (8 : Word) from rfl] at h] at hla
  have s36 := cpsTripleWithin_extend_code
    (ndaMem 36 (.SD .x6 .x18 (0 : BitVec 12)) (by decide) rfl)
    (sd_spec_gen_within .x6 .x18 ndaTopLoc newTop oldTop (0 : BitVec 12) (ndaAt 36))
  rw [ndaAt_succ 36, se0, add_zero_word] at s36
  have f36 := cpsTripleWithin_frameR R hR s36
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) hla f36
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c1

/-- **Indices 37-41: increment the record count.** -/
theorem nda_count_bump_spec (cnt v6 v7 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 5 (ndaAt 37) (ndaAt 42) ndaCr
      (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** (ndaCntLoc ↦ₘ cnt) ** R)
      (((.x6 : Reg) ↦ᵣ ndaCntLoc) ** ((.x7 : Reg) ↦ᵣ (cnt + (1 : Word))) **
        (ndaCntLoc ↦ₘ (cnt + (1 : Word))) ** R) := by
  have hla := la_seg_spec (ndaAt 37) .x6 ndaCntLoc v6 ndaCr
    (Codegen.laHi GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148))
    (Codegen.laLo GuestAddrs.mset_db_count (GuestAddrs.node_db_append + 148))
    (by decide) la37_hi la37_lo la37_range
    (ndaMem 37 _ (by decide) rfl)
    (by
      rw [ndaAt_succ 37]
      exact ndaMem 38 _ (by decide) rfl)
    (((.x7 : Reg) ↦ᵣ v7) ** (ndaCntLoc ↦ₘ cnt) ** R)
    (by pcf_r)
  rw [show (ndaAt 37 + 8 : Word) = ndaAt 39 from by
    have h := ndaAt_add 37 2
    rwa [show BitVec.ofNat 64 (4 * 2) = (8 : Word) from rfl] at h] at hla
  have s39 := cpsTripleWithin_extend_code
    (ndaMem 39 (.LD .x7 .x6 (0 : BitVec 12)) (by decide) rfl)
    (ld_spec_gen_within .x7 .x6 ndaCntLoc v7 cnt (0 : BitVec 12) (ndaAt 39) (by decide))
  rw [ndaAt_succ 39, se0, add_zero_word] at s39
  have f39 := cpsTripleWithin_frameR R hR s39
  have s40 := cpsTripleWithin_extend_code
    (ndaMem 40 (.ADDI .x7 .x7 (1 : BitVec 12)) (by decide) rfl)
    (addi_spec_gen_same_within .x7 cnt (1 : BitVec 12) (ndaAt 40) (by decide))
  rw [ndaAt_succ 40, se1] at s40
  have f40 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ ndaCntLoc) ** (ndaCntLoc ↦ₘ cnt) ** R)
    (by pcf_r) s40
  have s41 := cpsTripleWithin_extend_code
    (ndaMem 41 (.SD .x6 .x7 (0 : BitVec 12)) (by decide) rfl)
    (sd_spec_gen_within .x6 .x7 ndaCntLoc (cnt + (1 : Word)) cnt (0 : BitVec 12) (ndaAt 41))
  rw [ndaAt_succ 41, se0, add_zero_word] at s41
  have f41 := cpsTripleWithin_frameR R hR s41
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) hla f39
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f40
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f41
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c3

end EvmAsm.Codegen.NodeDbAppendSpec
