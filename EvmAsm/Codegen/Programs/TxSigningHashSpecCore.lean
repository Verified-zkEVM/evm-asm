/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecCore

  Scaffold + callWithins for K145 `tx_signing_hash` (#12038).

  Proof-only module. Pins `H := GuestAddrs.tx_signing_hash` (a REAL linked
  guest address — every `la`/`jalOff` in `txSigningHash_prog` is baked against
  that base and real callees). Models the top-level shape of
  `HeaderExtractNumberSpec.header_extract_number_spec_within`.

  ## Callee (multi-rate)

  `txSigningHash_prog` always JALs `zkvm_keccak256_segments` with a
  **3-segment** gather (type-prefix byte || RLP list-prefix || payload).
  The callee is the ungated multi-rate triple
  `zkvm_keccak256_segments_spec_within` (`kssCallerPost_multi` /
  `kssBodyFuelMulti`) — no `|msg| ≤ 135` INPUT-DOMAIN gate.

  ## Shape

  `txSigningHash_prog` (93 insn) = ABI frame (-64 / +64, 8 slots) around a
  74-instruction body with three cross-calls:
    `rlp_list_nth_item`, `rlp_encode_list_prefix`, `zkvm_keccak256_segments`.
-/

import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.TxSigningHashResidual
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTop
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.MemRegion
import EvmAsm.Stateless.SpecRef.Crypto

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashResidual
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef
open EvmAsm.Rv64.Tactics

/-! ## Linked base and ABI-frame decomposition -/

/-- Real linked guest entry of `tx_signing_hash`. -/
abbrev H : Word := BitVec.ofNat 64 GuestAddrs.tx_signing_hash

abbrev NthB : Word := BitVec.ofNat 64 GuestAddrs.rlp_list_nth_item
abbrev PrefixB : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_list_prefix
abbrev KssB' : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256_segments
abbrev TshBuf : Word := BitVec.ofNat 64 GuestAddrs.tsh_buf

/-- Frame: `ra` + `s0 s1 s2 s3 s4 s5 s6` — matches the emitted saves. -/
def tshFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]


def tshBody : List Instr :=  [
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56)),
    .SB .x5 .x19 (0 : BitVec 12),
    .BEQ .x9 .x0 (260 : BitVec 13),
    .LBU .x5 .x8 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (248 : BitVec 13),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (16 : BitVec 13),
    .ADDI .x21 .x5 (-247 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x21 (1 : Word),
    .LI .x22 (0 : Word),
    .BEQ .x18 .x0 (76 : BitVec 13),
    .ADDI .x5 .x18 (-1 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x5,
    .AUIPC .x13 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132)),
    .ADDI .x13 .x13 (64 : BitVec 12),
    .AUIPC .x14 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144)),
    .ADDI .x14 .x14 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144)),
    .ADDI .x14 .x14 (72 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_signing_hash + 156)),
    .BNE .x10 .x0 (168 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164)),
    .LD .x6 .x5 (64 : BitVec 12),
    .LD .x7 .x5 (72 : BitVec 12),
    .ADD .x6 .x6 .x7,
    .SUB .x22 .x6 .x21,
    .MV .x10 .x22,
    .AUIPC .x11 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192)),
    .ADDI .x11 .x11 (16 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204)),
    .ADDI .x12 .x12 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.tx_signing_hash + 216)),
    .AUIPC .x5 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220)),
    .LD .x29 .x5 (80 : BitVec 12),
    .AUIPC .x30 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232)),
    .ADDI .x30 .x30 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232)),
    .ADDI .x30 .x30 (128 : BitVec 12),
    .LI .x5 (0 : Word),
    .BEQ .x19 .x0 (8 : BitVec 13),
    .LI .x5 (1 : Word),
    .AUIPC .x31 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256)),
    .ADDI .x31 .x31 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256)),
    .SD .x30 .x31 (0 : BitVec 12),
    .SD .x30 .x5 (8 : BitVec 12),
    .AUIPC .x31 (laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272)),
    .ADDI .x31 .x31 (laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272)),
    .ADDI .x31 .x31 (16 : BitVec 12),
    .SD .x30 .x31 (16 : BitVec 12),
    .SD .x30 .x29 (24 : BitVec 12),
    .ADD .x31 .x8 .x21,
    .SD .x30 .x31 (32 : BitVec 12),
    .SD .x30 .x22 (40 : BitVec 12),
    .MV .x10 .x30,
    .LI .x11 (3 : Word),
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256_segments (GuestAddrs.tx_signing_hash + 316)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word)
  ]



theorem tshBody_length : tshBody.length = 74 := by decide

theorem tshFrame_length : tshFrame.length = 8 := by decide

/-- Byte-identity: the emitted Program IS the ABI frame around `tshBody`. -/
theorem txSigningHash_prog_eq_abiFrame :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) tshFrame tshBody
      = txSigningHash_prog := rfl

theorem tsh_prog_length : txSigningHash_prog.length = 93 := by decide

/-! ## CodeReq closure (wrapper ∪ three callees) -/

def tshCode : CodeReq := CodeReq.ofProg H txSigningHash_prog

def nthCode : CodeReq := EvmAsm.Codegen.RlpListNthItemSAsm.code

def prefixCode : CodeReq := CodeReq.ofProg PrefixB rlpEncodeListPrefix_prog

def kssCode : CodeReq := kssCr

/-- Full linked image used by the whole-routine triple. -/
def fullCode : CodeReq :=
  tshCode.union (nthCode.union (prefixCode.union kssCode))

theorem tsh_nth_disjoint : tshCode.Disjoint nthCode := by
  unfold tshCode nthCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [tsh_prog_length]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [tsh_prog_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide

theorem tsh_prefix_disjoint : tshCode.Disjoint prefixCode := by
  unfold tshCode prefixCode
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [tsh_prog_length]; decide
  · decide
  · rw [tsh_prog_length]; decide

theorem tsh_kss_disjoint : tshCode.Disjoint kssCode := by
  unfold tshCode kssCode kssCr
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [tsh_prog_length]; decide
  · rw [kssProgL_len]; decide
  · rw [tsh_prog_length, kssProgL_len]; decide

theorem tsh_mono : ∀ a i, tshCode a = some i → fullCode a = some i := by
  intro a i hi
  unfold fullCode
  exact CodeReq.union_mono_left a i hi

theorem nth_prefix_disjoint : nthCode.Disjoint prefixCode := by
  unfold nthCode prefixCode EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide

theorem nth_kss_disjoint : nthCode.Disjoint kssCode := by
  unfold nthCode kssCode kssCr EvmAsm.Codegen.RlpListNthItemSAsm.code
  apply CodeReq.Disjoint.ofProg_ranges
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · rw [kssProgL_len]; decide
  · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length, kssProgL_len]; decide

theorem prefix_kss_disjoint : prefixCode.Disjoint kssCode := by
  unfold prefixCode kssCode kssCr
  apply CodeReq.Disjoint.ofProg_ranges
  · decide
  · rw [kssProgL_len]; decide
  · rw [kssProgL_len]; decide

/-- `kssCode ⊆ fullCode` via pairwise misses + `union_skip` (avoids
    `mono_union_right` whnf on nested `ofProg` Disjoints). -/
theorem kss_mono : ∀ a i, kssCode a = some i → fullCode a = some i := by
  intro a i hi
  have htsh : tshCode a = none := by
    cases tsh_kss_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hnth : nthCode a = none := by
    cases nth_kss_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hpre : prefixCode a = none := by
    cases prefix_kss_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (tshCode.union (nthCode.union (prefixCode.union kssCode))) a = some i
  exact CodeReq.union_skip htsh
    (CodeReq.union_skip hnth (CodeReq.union_skip hpre hi))

/-- `nthCode ⊆ fullCode` — skip TSH head, then hit nth. -/
theorem nth_mono : ∀ a i, nthCode a = some i → fullCode a = some i := by
  intro a i hi
  have htsh : tshCode a = none := by
    cases tsh_nth_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (tshCode.union (nthCode.union (prefixCode.union kssCode))) a = some i
  exact CodeReq.union_skip htsh (CodeReq.union_hit hi)

/-- Discharge `CodeReq.singleton` for an instruction of the emitted Program. -/
theorem tshMem (prog : List Instr) (hprog : prog = (txSigningHash_prog : List Instr))
    (A : Word) (k : Nat) (ins : Instr)
    (hk : k < prog.length)
    (hA : A = H + BitVec.ofNat 64 (4 * k))
    (hins : prog[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → fullCode a = some i := by
  subst hprog
  intro a i hs
  unfold fullCode
  apply CodeReq.union_mono_left
  exact CodeReq.ofProg_mem_at H A (txSigningHash_prog : List Instr) k ins hA hk hins
    (by rw [tsh_prog_length]; norm_num) a i hs

/-! ## Cross-call PCs (real GuestAddrs offsets) -/

abbrev tshNthJalPC : Word := H + BitVec.ofNat 64 156
abbrev tshPrefixJalPC : Word := H + BitVec.ofNat 64 216
abbrev tshKssJalPC : Word := H + BitVec.ofNat 64 316

def tshNthJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.tx_signing_hash + 156)

def tshPrefixJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.tx_signing_hash + 216)

def tshKssJalOff : BitVec 21 :=
  jalOff GuestAddrs.zkvm_keccak256_segments (GuestAddrs.tx_signing_hash + 316)

theorem tshNthJal_target : tshNthJalPC + signExtend21 tshNthJalOff = NthB := by
  unfold tshNthJalPC tshNthJalOff H NthB; decide

theorem tshPrefixJal_target : tshPrefixJalPC + signExtend21 tshPrefixJalOff = PrefixB := by
  unfold tshPrefixJalPC tshPrefixJalOff H PrefixB; decide

theorem tshKssJal_target : tshKssJalPC + signExtend21 tshKssJalOff = KssB' := by
  unfold tshKssJalPC tshKssJalOff H KssB'; decide

theorem tshKssJal_ret_even :
    ((tshKssJalPC + 4) &&& ~~~(1 : Word)) = tshKssJalPC + 4 := by
  unfold tshKssJalPC H; decide

theorem tshKssJal_mem :
    ∀ a i, CodeReq.singleton tshKssJalPC (.JAL .x1 tshKssJalOff) a = some i →
      fullCode a = some i :=
  tshMem (txSigningHash_prog : List Instr) rfl tshKssJalPC 79
    (.JAL .x1 tshKssJalOff)
    (by simpa [Program] using (by rw [tsh_prog_length]; decide))
    (by unfold tshKssJalPC H; decide) rfl

theorem tshNthJal_mem :
    ∀ a i, CodeReq.singleton tshNthJalPC (.JAL .x1 tshNthJalOff) a = some i →
      fullCode a = some i :=
  tshMem (txSigningHash_prog : List Instr) rfl tshNthJalPC 39
    (.JAL .x1 tshNthJalOff)
    (by simpa [Program] using (by rw [tsh_prog_length]; decide))
    (by unfold tshNthJalPC H; decide) rfl

theorem tshPrefixJal_mem :
    ∀ a i, CodeReq.singleton tshPrefixJalPC (.JAL .x1 tshPrefixJalOff) a = some i →
      fullCode a = some i :=
  tshMem (txSigningHash_prog : List Instr) rfl tshPrefixJalPC 54
    (.JAL .x1 tshPrefixJalOff)
    (by simpa [Program] using (by rw [tsh_prog_length]; decide))
    (by unfold tshPrefixJalPC H; decide) rfl

theorem KssB'_eq : KssB' = KssB := rfl

/-! ## Multi-rate segments triple, lifted into `fullCode`

    Reuses ungated `zkvm_keccak256_segments_spec_within` at the real linked
    `GuestAddrs.zkvm_keccak256_segments` base. -/

theorem tsh_kss_in_fullCode
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let vals := kssEntryVals ret v8 v9 v18 v19 v20 v21 v22
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    cpsTripleWithin (19 + kssBodyFuelMulti segs) KssB' ret fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsOwn kssFrame newSp **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost_multi segsBase outputBase segs A) := by
  intro vals newSp
  have h := zkvm_keccak256_segments_spec_within sp0 ret segsBase outputBase
    segs os v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA halign_ret hos hcount hsegs
  simpa [KssB'_eq] using cpsTripleWithin_extend_code kss_mono h

/-- Factor `ra` out of `regsAt kssFrame` for `callWithin_spec`. -/
theorem tsh_kssRegs_factor (ret v8 v9 v18 v19 v20 v21 v22 : Word) :
    regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) =
      ((.x1 ↦ᵣ ret) **
        ((.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
          (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22))) := by
  simp only [regsAt, kssFrame, kssEntryVals, List.foldr, sepConj_emp_right']

/-- Callee-saved s-regs of the segments frame (no `ra`). -/
def tshKssSregs (v8 v9 v18 v19 v20 v21 v22 : Word) : Assertion :=
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
    (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22)

theorem tshKssSregs_pcFree (v8 v9 v18 v19 v20 v21 v22 : Word) :
    (tshKssSregs v8 v9 v18 v19 v20 v21 v22).pcFree := by
  unfold tshKssSregs
  repeat first | apply pcFree_sepConj | exact pcFree_regIs

/-- Call-site pre without `ra` (owned by `callWithin_spec`). -/
def tshKssCallPre (sp0 newSp segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ sp0) ** tshKssSregs v8 v9 v18 v19 v20 v21 v22 **
    frameSlotsOwn kssFrame newSp **
    kssCallerPre segsBase outputBase segs os v5 v6 v7 A

/-- Call-site post without `ra`. -/
def tshKssCallPost (sp0 newSp ret segsBase outputBase : Word) (segs : List KssSeg)
    (v8 v9 v18 v19 v20 v21 v22 : Word) (A : Assertion) : Assertion :=
  (.x2 ↦ᵣ sp0) ** tshKssSregs v8 v9 v18 v19 v20 v21 v22 **
    frameSlotsSaved kssFrame newSp (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
    kssCallerPost_multi segsBase outputBase segs A

theorem tshKssCallPre_pcFree (sp0 newSp segsBase outputBase : Word)
    (segs : List KssSeg) (os : List (BitVec 8))
    (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word) (A : Assertion)
    (hA : A.pcFree) :
    (tshKssCallPre sp0 newSp segsBase outputBase segs os
      v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A).pcFree := by
  unfold tshKssCallPre
  exact pcFree_sepConj pcFree_regIs
    (pcFree_sepConj (tshKssSregs_pcFree _ _ _ _ _ _ _)
      (pcFree_sepConj (pcFree_frameSlotsOwn _ _)
        (kssCallerPre_pcFree _ _ _ _ _ _ _ _ hA)))

/-- Reshape the lifted segments triple so `ra` is the `callWithin` head. -/
theorem tsh_kss_ra_factored
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin fuel KssB' ret fullCode
      (((.x1 ↦ᵣ ret) **
        tshKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A))
      (((.x1 ↦ᵣ ret) **
        tshKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A)) := by
  intro newSp fuel
  have hcore := tsh_kss_in_fullCode sp0 ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA halign_ret hos hcount hsegs
  -- hcore pre/post still under `let vals` / `let newSp`; reduce them.
  change cpsTripleWithin (19 + kssBodyFuelMulti segs) KssB' ret fullCode
    ((.x2 ↦ᵣ sp0) **
      regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      frameSlotsOwn kssFrame newSp **
      kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
    ((.x2 ↦ᵣ sp0) **
      regsAt kssFrame (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      frameSlotsSaved kssFrame newSp (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
      kssCallerPost_multi segsBase outputBase segs A) at hcore
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hcore
  · -- P' → P: expand CallPre; split goal regsAt; xperm
    unfold tshKssCallPre tshKssSregs at hp
    rw [tsh_kssRegs_factor]
    xperm_hyp hp
  · -- Q → Q': split hq regsAt; fold into CallPost; xperm
    unfold tshKssCallPost tshKssSregs
    rw [tsh_kssRegs_factor] at hq
    xperm_hyp hq

/-- **`callWithin` at `tx_signing_hash+316` (multi-rate segments).** -/
theorem tsh_kss_callWithin
    (vOld sp0 segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let ret := tshKssJalPC + 4
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin (1 + fuel) tshKssJalPC ret fullCode
      (((.x1 ↦ᵣ vOld) **
        (tshKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A ** F)))
      (((.x1 ↦ᵣ ret) **
        (tshKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A ** F))) := by
  intro ret newSp fuel
  have hret_even : (ret &&& ~~~(1 : Word)) = ret := tshKssJal_ret_even
  have hcallee := tsh_kss_ra_factored sp0 ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA hret_even hos hcount hsegs
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP := pcFree_sepConj
    (tshKssCallPre_pcFree sp0 newSp segsBase outputBase segs os
      v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA) hF
  exact callWithin_spec tshKssJalPC KssB' vOld tshKssJalOff fuel
    tshKssJal_target tshKssJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)

/-! ## `rlp_list_nth_item` callWithin at `tx_signing_hash+156` -/

abbrev tshNthOffPtr : Word := TshBuf + 64
abbrev tshNthLenPtr : Word := TshBuf + 72

theorem tshNthJal_ret_even :
    ((tshNthJalPC + 4) &&& ~~~(1 : Word)) = tshNthJalPC + 4 := by
  unfold tshNthJalPC H; decide

/-- **`rlp_list_nth_item` callWithin at the real K145 jal site.** -/
theorem tsh_nth_callWithin
    (vOld sp0 listBase listLenW indexW oldOffset oldLen : Word)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (F : Assertion) (hF : F.pcFree)
    (hlistLenW : listLenW = BitVec.ofNat 64 listLen)
    (hindexW : indexW = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
      (1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9))
      tshNthJalPC (tshNthJalPC + 4) fullCode
      (((.x1 ↦ᵣ vOld) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callEntryRest sp0 listBase listLenW indexW
          tshNthOffPtr tshNthLenPtr oldOffset oldLen
          { saved with ra := tshNthJalPC + 4 } bytes) ** F)
      (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 listBase indexW
          tshNthOffPtr tshNthLenPtr oldOffset oldLen
          { saved with ra := tshNthJalPC + 4 } bytes listLen index) ** F) := by
  exact EvmAsm.Codegen.RlpListNthItemSAsm.rlpListNthItem_call_spec_within
    (cr := fullCode) (callerPC := tshNthJalPC) (calleeEntry := NthB)
    vOld sp0 listBase listLenW indexW tshNthOffPtr tshNthLenPtr
    oldOffset oldLen tshNthJalOff F hF saved bytes listLen index
    hlistLenW hindexW hindex hsalign (by omega) (by omega) hover hvalid (by omega)
    tshNthJal_ret_even tshNthJal_target rfl tshNthJal_mem nth_mono

/-! ## Short `rlp_encode_list_prefix` lifted into `fullCode` -/

theorem prefix_mono : ∀ a i, prefixCode a = some i → fullCode a = some i := by
  intro a i hi
  have htsh : tshCode a = none := by
    cases tsh_prefix_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  have hnth : nthCode a = none := by
    cases nth_prefix_disjoint a with
    | inl h => exact h
    | inr h => rw [h] at hi; cases hi
  change (tshCode.union (nthCode.union (prefixCode.union kssCode))) a = some i
  exact CodeReq.union_skip htsh
    (CodeReq.union_skip hnth (CodeReq.union_hit hi))

theorem tsh_prefix_short_in_fullCode
    (len outPtr cellPtr raVal v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 8 PrefixB (raVal &&& ~~~1) fullCode
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
       (cellPtr ↦ₘ (1 : Word))) :=
  cpsTripleWithin_extend_code prefix_mono
    (EvmAsm.Codegen.RlpSpliceHelperSpec.rlp_encode_list_prefix_short_pinned_spec_within
      PrefixB len outPtr cellPtr
      raVal v5 v6 v7 outBytes cellOld h_len h_out_align h_out_len h_out_valid)

theorem tshPrefixJal_ret_even :
    ((tshPrefixJalPC + 4) &&& ~~~(1 : Word)) = tshPrefixJalPC + 4 := by
  unfold tshPrefixJalPC H; decide

/-- Short list-prefix `callWithin` at `tx_signing_hash+216`.
    Gate `len.toNat < 56` matches the short path of `rlp_encode_list_prefix`
    (residual INPUT-DOMAIN gate after multi-rate keccak re-point). -/
theorem tsh_prefix_short_callWithin
    (vOld len outPtr cellPtr v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    let ret := tshPrefixJalPC + 4
    cpsTripleWithin (1 + 8) tshPrefixJalPC ret fullCode
      (((.x1 ↦ᵣ vOld) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
         (cellPtr ↦ₘ (1 : Word)) ** F))) := by
  intro ret
  have hret_eq : (ret &&& ~~~(1 : Word)) = ret := tshPrefixJal_ret_even
  have hcore := tsh_prefix_short_in_fullCode len outPtr cellPtr ret v5 v6 v7
    outBytes cellOld h_len h_out_align h_out_len h_out_valid
  rw [hret_eq] at hcore
  have hcallee : cpsTripleWithin 8 PrefixB ret fullCode
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))))
      (((.x1 ↦ᵣ ret) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
         ((.x12 : Reg) ↦ᵣ cellPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
         (cellPtr ↦ₘ (1 : Word))))) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcore
  have hcalleeF := cpsTripleWithin_frameR F hF hcallee
  have hP : ((((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
      ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
      ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld) ** F)).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  exact callWithin_spec tshPrefixJalPC PrefixB vOld tshPrefixJalOff 8
    tshPrefixJal_target tshPrefixJal_mem hP
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcalleeF)

end EvmAsm.Codegen.TxSigningHashSpec
