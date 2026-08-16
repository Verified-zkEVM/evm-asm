/-
  Structural decomposition for K146 `tx_signing_hash_legacy_eip155`.

  The linked routine is an ABI frame around a 101-instruction body.  Keeping
  this fact separate from the semantic body proof makes the frame entry/exit
  addresses explicit without treating the body contract as an assumption.
-/

import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTop
import EvmAsm.Rv64.SAsm.AbiFrame

namespace EvmAsm.Codegen.TxSigningHashLegacySpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.Proofs

abbrev legacyH : Word := BitVec.ofNat 64 GuestAddrs.tx_signing_hash_legacy_eip155

def legacyFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]

def legacyBody : List Instr :=
  (txSigningHashLegacyEip155_prog.drop 9).take 101

def legacyCode : CodeReq := CodeReq.ofProg legacyH txSigningHashLegacyEip155_prog

abbrev legacyNthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
abbrev legacyUintB : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_uint_be
abbrev legacyPrefixB : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_list_prefix
abbrev legacyKssB : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256_segments

def legacyNthCode : CodeReq := EvmAsm.Codegen.RlpListNthItemSAsm.code
def legacyUintCode : CodeReq := EvmAsm.Codegen.RlpEncodeUintBeSAsm.reubCode
def legacyPrefixCode : CodeReq := CodeReq.ofProg legacyPrefixB rlpEncodeListPrefix_prog
def legacyKssCode : CodeReq := kssCr

/-- Full linked image used by the K146 body composition. -/
def legacyFullCode : CodeReq :=
  legacyCode.union (legacyNthCode.union
    (legacyUintCode.union (legacyPrefixCode.union legacyKssCode)))

abbrev legacyBodyEntry : Word := legacyH + BitVec.ofNat 64 36
abbrev legacyBodyExit : Word := legacyH + BitVec.ofNat 64 440

theorem legacyFrame_length : legacyFrame.length = 8 := by decide

theorem legacyBody_length : legacyBody.length = 101 := by decide

theorem legacy_prog_length : txSigningHashLegacyEip155_prog.length = 120 := by decide

theorem legacy_prog_eq_abiFrame :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) legacyFrame legacyBody =
      txSigningHashLegacyEip155_prog := by decide

theorem legacyBodyEntry_eq :
    legacyH + BitVec.ofNat 64 (4 * (1 + legacyFrame.length)) = legacyBodyEntry := by
  rw [legacyFrame_length]

theorem legacyBodyExit_eq :
    legacyH + BitVec.ofNat 64
      (4 * (1 + legacyFrame.length + legacyBody.length)) = legacyBodyExit := by
  rw [legacyFrame_length, legacyBody_length]

theorem legacyCode_mono : ∀ a i, legacyCode a = some i → legacyFullCode a = some i := by
  intro a i hi
  exact CodeReq.union_mono_left a i hi

theorem legacyNth_disjoint : legacyCode.Disjoint legacyNthCode := by
  unfold legacyCode legacyNthCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [legacy_prog_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [legacy_prog_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide

theorem legacyUint_disjoint : legacyCode.Disjoint legacyUintCode := by
  unfold legacyCode legacyUintCode EvmAsm.Codegen.RlpEncodeUintBeSAsm.reubCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [legacy_prog_length]; decide
  · rw [EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_prog_length]; decide
  · rw [legacy_prog_length, EvmAsm.Codegen.RlpEncodeUintBeSAsm.reub_prog_length]; decide

theorem legacyPrefix_disjoint : legacyCode.Disjoint legacyPrefixCode := by
  unfold legacyCode legacyPrefixCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [legacy_prog_length]; decide
  · decide
  · rw [legacy_prog_length]; decide

theorem legacyKss_disjoint : legacyCode.Disjoint legacyKssCode := by
  unfold legacyCode legacyKssCode kssCr
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [legacy_prog_length]; decide
  · rw [kssProgL_len]; decide
  · rw [legacy_prog_length, kssProgL_len]; decide

theorem legacyNth_mono : ∀ a i, legacyNthCode a = some i → legacyFullCode a = some i := by
  intro a i hi
  have hlegacy : legacyCode a = none := by
    cases legacyNth_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (legacyCode.union (legacyNthCode.union
    (legacyUintCode.union (legacyPrefixCode.union legacyKssCode)))) a = some i
  exact CodeReq.union_skip hlegacy (CodeReq.union_hit hi)

abbrev legacyNthJalPC : Word := legacyH + BitVec.ofNat 64 120
abbrev legacyNthOffPtr : Word := BitVec.ofNat 64 GuestAddrs.t155_buf + 64
abbrev legacyNthLenPtr : Word := BitVec.ofNat 64 GuestAddrs.t155_buf + 72

def legacyNthJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_list_nth_item
    (GuestAddrs.tx_signing_hash_legacy_eip155 + 120)

theorem legacyNthJal_target :
    legacyNthJalPC + signExtend21 legacyNthJalOff = legacyNthB := by
  unfold legacyNthJalPC legacyNthJalOff legacyH legacyNthB
  decide

theorem legacyNthJal_ret_even :
    ((legacyNthJalPC + 4) &&& ~~~(1 : Word)) = legacyNthJalPC + 4 := by
  unfold legacyNthJalPC legacyH
  decide

theorem legacyNthJal_mem :
    ∀ a i, CodeReq.singleton legacyNthJalPC (.JAL .x1 legacyNthJalOff) a = some i →
      legacyFullCode a = some i := by
  intro a i hi
  have h := CodeReq.ofProg_mem_at legacyH legacyNthJalPC
    (txSigningHashLegacyEip155_prog : List Instr) 30
    (.JAL .x1 legacyNthJalOff)
    (by unfold legacyNthJalPC legacyH; decide)
    (by rw [legacy_prog_length]; decide)
    (by rfl) (by rw [legacy_prog_length]; norm_num) a i hi
  exact legacyCode_mono a i h

/-- The K146 `rlp_list_nth_item` call at `H+120`, with its actual ABI
    registers and scratch cells.  The caller body supplies the saved-frame
    values; this adapter deliberately does not assume that the parse succeeds. -/
theorem legacyNth_callWithin
    (vOld sp0 listBase listLenW oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (5 + 2)) + 6)) + 9))
      legacyNthJalPC (legacyNthJalPC + 4) legacyFullCode
      (((.x1 ↦ᵣ vOld) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callEntryRest sp0 listBase listLenW
          (5 : Word) legacyNthOffPtr legacyNthLenPtr oldOffset oldLen
          { saved with ra := legacyNthJalPC + 4 } bytes) ** F)
      (((.x1 ↦ᵣ (legacyNthJalPC + 4)) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 listBase (5 : Word)
          legacyNthOffPtr legacyNthLenPtr oldOffset oldLen
          { saved with ra := legacyNthJalPC + 4 } bytes listLen 5) ** F) := by
  exact EvmAsm.Codegen.RlpListNthItemSAsm.rlpListNthItem_call_spec_within
    (cr := legacyFullCode) (callerPC := legacyNthJalPC) (calleeEntry := legacyNthB)
    vOld sp0 listBase listLenW (5 : Word) legacyNthOffPtr legacyNthLenPtr
    oldOffset oldLen legacyNthJalOff F hF saved bytes listLen 5
    hlistLenW rfl (by decide) hsalign (by omega) (by omega) hover hvalid (by omega)
    legacyNthJal_ret_even legacyNthJal_target rfl legacyNthJal_mem legacyNth_mono

end EvmAsm.Codegen.TxSigningHashLegacySpec
