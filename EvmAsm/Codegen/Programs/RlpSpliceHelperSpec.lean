/-
  EvmAsm.Codegen.Programs.RlpSpliceHelperSpec

  Lives under Codegen/Programs (not Evm64) because it pins the concrete
  linked guest entries (`GuestAddrs.rlp_item_size`,
  `GuestAddrs.rlp_encode_list_prefix`) of `Codegen.Programs.RlpRead`
  routines (layering L1: verified core may not import Codegen) — same
  shape as `AccountBalanceHelperSpec.lean`.

  Phase 3c part 2 (SELFDESTRUCT effects-body chain, `mpt_splice_slot` →
  `account_set_uint_field` → `selfdestruct_balance_transfer`):
  success-path `cpsTripleWithin` triples for the RLP codegen splice
  helpers.

  This file proves:

  * `rlp_item_size` (`rlpItemSize_prog`, 35 instructions) — the full
    encoded byte span of one RLP item at `a0`, the leaf callee of
    `rlp_item_span`.  Covered forms (the complete account path — every
    account field is a scalar/short string, plus embedded short lists):
      - single byte  (`b < 0x80`)               → span 1
      - short string (`0x80 ≤ b ≤ 0xb7`)        → span `b - 0x80 + 1`
        (covers empty `0x80`, `0x81+b`, and `0xa0+32` storageRoot/codeHash)
      - short list   (`0xc0 ≤ b ≤ 0xf7`)        → span `b - 0xc0 + 1`
    Each form has a `∀ base` triple; `rlp_item_size_form_spec_within`
    is the unified dispatch whose post ties `a0` to the PURE layer:
    `a0 = (EL.RLP.encode item).length` for any successful
    `EL.RLP.decode` of the buffer (via `decode_eq_some_imp_encode`).
    The long-string/long-list forms (`0xb8..0xbf`, `0xf8..`, with the
    length-of-length accumulate loop) are NOT covered here.

  * `rlp_encode_list_prefix` (`rlpEncodeListPrefix_prog`, 46
    instructions) — writes the RLP list-header bytes for a payload
    length `a0` into `a1` and the header length into the u64 cell `a2`:
      - short form  (`len < 56`)        → `[0xC0 + len]`, header len 1
      - long-1 form (`56 ≤ len < 256`)  → `[0xF8, len]`,   header len 2
        (the account list is ALWAYS this form, cf. `encodeAccount_eq_cons`)
    `rlp_encode_list_prefix_spec_within` is the unified dispatch; the
    bridge `encode_list_eq_prefix_append` ties the written bytes to the
    header of `EL.RLP.encode (.list items)`.  The `lenlen ≥ 2` long
    forms (payload ≥ 256 bytes) are NOT covered.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Evm64.CallingConvention
import EvmAsm.EL.RLP.Properties
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpSpliceHelperArithmetic
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

namespace RlpSpliceHelperSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

/-- Code-membership for a `∀ base` `ofProg` slice: instruction `k` of the
    program, addressed as a concrete `base + OFF` term. -/
local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr _ _ $k _ (by decide) (by decide) (by bv_omega)))

/-! ## `rlp_item_size` — per-form `∀ base` triples

    ABI (`RlpRead.lean`): `a0` = ptr to one RLP item → `a0` = its full
    encoded size; leaf, clobbers `t0`/`t1` (`x5`/`x6`) on these paths,
    preserves everything else, returns to `ra &&& ~~~1`. -/

/-- **`rlp_item_size`, single-byte form** (`bs[0] < 0x80` → `a0 = 1`),
    with the scratch registers pinned. -/
theorem rlp_item_size_single_pinned_spec_within (base ptr raVal v5 v6 : Word)
    (bs : List (BitVec 8))
    (h_align : ptr.toNat % 8 = 0)
    (h_len : 0 < bs.length)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_b : (bs.getD 0 0).toNat < 0x80) :
    cpsTripleWithin 5 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  set CR := CodeReq.ofProg base rlpItemSize_prog with hCR
  have h0 : (bs[0]'h_len) = bs.getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_len]; rfl
  -- idx0 (base+0): LBU x5, 0(x10)
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 ptr v5 base bs 0 (by decide) h_align h_len
      (by have := ptr.isLt; omega) (h_valid 0 h_len))
    (by rw [hCR]; cmem 0)
  rw [show ptr + BitVec.ofNat 64 0 = ptr from by bv_omega, h0] at hlbu
  -- idx1 (base+4): LI x6, 0x80
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli
  -- idx2 (base+8): BGEU x5, x6, +12 — NOT taken (b < 0x80)
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr
  have hult : BitVec.ult ((bs.getD 0 0).zeroExtend 64) (0x80 : Word) :=
    ult_zx_of_lt _ _ (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; exact h_b)
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult)
  -- idx3 (base+12): LI x10, 1
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x10 ptr (1 : Word) (base + 12) (by decide))
    (by rw [hCR]; cmem 3)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hli10
  -- idx4 (base+16): ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 16) raVal)
    (by rw [hCR]; cmem 4)
  -- frames
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hli
  have hntF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hnt
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0x80 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hli10
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0x80 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) hret
  -- compose
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hntF
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli10F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc4
  have hq1 : (((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0x80 : Word)) **
       (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
  xperm_hyp hq2

/-- **`rlp_item_size`, short-string form**
    (`0x80 ≤ bs[0] ≤ 0xb7` → `a0 = bs[0] - 0x80 + 1 = bs[0] - 127`),
    with the scratch registers pinned. -/
theorem rlp_item_size_short_string_pinned_spec_within (base ptr raVal v5 v6 : Word)
    (bs : List (BitVec 8))
    (h_align : ptr.toNat % 8 = 0)
    (h_len : 0 < bs.length)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_lo : 0x80 ≤ (bs.getD 0 0).toNat)
    (h_hi : (bs.getD 0 0).toNat < 0xb8) :
    cpsTripleWithin 8 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs.getD 0 0).toNat - 127)) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  set CR := CodeReq.ofProg base rlpItemSize_prog with hCR
  have h0 : (bs[0]'h_len) = bs.getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_len]; rfl
  -- idx0 (base+0): LBU x5, 0(x10)
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 ptr v5 base bs 0 (by decide) h_align h_len
      (by have := ptr.isLt; omega) (h_valid 0 h_len))
    (by rw [hCR]; cmem 0)
  rw [show ptr + BitVec.ofNat 64 0 = ptr from by bv_omega, h0] at hlbu
  -- idx1 (base+4): LI x6, 0x80
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli
  -- idx2 (base+8): BGEU x5, x6, +12 — TAKEN (b ≥ 0x80) → base+20
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr
  have hnult : ¬ BitVec.ult ((bs.getD 0 0).zeroExtend 64) (0x80 : Word) :=
    not_ult_zx_of_ge _ _ (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; exact h_lo)
  have ht2 := cpsBranchWithin_takenStripPure2 hbr (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact hnult ((sepConj_pure_right _).1 hQ).2)
  -- idx5 (base+20): LI x6, 0xb8
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 20) (by decide))
    (by rw [hCR]; cmem 5)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hli5
  -- idx6 (base+24): BGEU x5, x6, +16 — NOT taken (b < 0xb8) → base+28
  have hbr6 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 6)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xb8 : Word) (base + 24))
  rw [show (base + 24 : Word) + signExtend13 (16 : BitVec 13) = base + 40 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbr6
  have hult6 : BitVec.ult ((bs.getD 0 0).zeroExtend 64) (0xb8 : Word) :=
    ult_zx_of_lt _ _ (by rw [show ((0xb8 : Word)).toNat = 184 from by decide]; exact h_hi)
  have hnt6 := cpsBranchWithin_ntakenStripPure2 hbr6 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult6)
  -- idx7 (base+28): ADDI x10, x5, -128
  have ha7 := liftCode (cr' := CR)
    (addi_spec_gen_within .x10 .x5 ptr ((bs.getD 0 0).zeroExtend 64)
      (-128 : BitVec 12) (base + 28) (by decide))
    (by rw [hCR]; cmem 7)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at ha7
  -- idx8 (base+32): ADDI x10, x10, 1
  have ha8 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x10
      (((bs.getD 0 0).zeroExtend 64) + signExtend12 (-128 : BitVec 12))
      (1 : BitVec 12) (base + 32) (by decide))
    (by rw [hCR]; cmem 8)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega,
      ris_result_128 _ h_lo] at ha8
  -- idx9 (base+36): ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 36) raVal)
    (by rw [hCR]; cmem 9)
  -- frames
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hli
  have ht2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) ht2
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hli5
  have hnt6F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hnt6
  have ha7F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ (0xb8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha7
  have ha8F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xb8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) ha8
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs.getD 0 0).toNat - 127)) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xb8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hret
  -- compose
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 ht2F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli5F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 hnt6F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 ha7F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 ha8F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc7
  have hq1 : (((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0xb8 : Word)) **
       (((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs.getD 0 0).toNat - 127)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
  xperm_hyp hq2

/-- **`rlp_item_size`, short-list form**
    (`0xc0 ≤ bs[0] ≤ 0xf7` → `a0 = bs[0] - 0xc0 + 1 = bs[0] - 191`),
    with the scratch registers pinned. -/
theorem rlp_item_size_short_list_pinned_spec_within (base ptr raVal v5 v6 : Word)
    (bs : List (BitVec 8))
    (h_align : ptr.toNat % 8 = 0)
    (h_len : 0 < bs.length)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_lo : 0xc0 ≤ (bs.getD 0 0).toNat)
    (h_hi : (bs.getD 0 0).toNat < 0xf8) :
    cpsTripleWithin 12 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs.getD 0 0).toNat - 191)) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  set CR := CodeReq.ofProg base rlpItemSize_prog with hCR
  have h0 : (bs[0]'h_len) = bs.getD 0 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_len]; rfl
  -- idx0 (base+0): LBU x5, 0(x10)
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 ptr v5 base bs 0 (by decide) h_align h_len
      (by have := ptr.isLt; omega) (h_valid 0 h_len))
    (by rw [hCR]; cmem 0)
  rw [show ptr + BitVec.ofNat 64 0 = ptr from by bv_omega, h0] at hlbu
  -- idx1 (base+4): LI x6, 0x80
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli
  -- idx2 (base+8): BGEU x5, x6, +12 — TAKEN (b ≥ 0xc0 ≥ 0x80) → base+20
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr
  have ht2 := cpsBranchWithin_takenStripPure2 hbr (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0x80 : Word)
        (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- idx5 (base+20): LI x6, 0xb8
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 20) (by decide))
    (by rw [hCR]; cmem 5)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hli5
  -- idx6 (base+24): BGEU x5, x6, +16 — TAKEN (b ≥ 0xc0 ≥ 0xb8) → base+40
  have hbr6 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 6)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xb8 : Word) (base + 24))
  rw [show (base + 24 : Word) + signExtend13 (16 : BitVec 13) = base + 40 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbr6
  have ht6 := cpsBranchWithin_takenStripPure2 hbr6 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xb8 : Word)
        (by rw [show ((0xb8 : Word)).toNat = 184 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- idx10 (base+40): LI x6, 0xc0
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 40) (by decide))
    (by rw [hCR]; cmem 10)
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hli10
  -- idx11 (base+44): BGEU x5, x6, +16 — TAKEN (b ≥ 0xc0) → base+60
  have hbr11 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 11)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xc0 : Word) (base + 44))
  rw [show (base + 44 : Word) + signExtend13 (16 : BitVec 13) = base + 60 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hbr11
  have ht11 := cpsBranchWithin_takenStripPure2 hbr11 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xc0 : Word)
        (by rw [show ((0xc0 : Word)).toNat = 192 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  -- idx15 (base+60): LI x6, 0xf8
  have hli15 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 60) (by decide))
    (by rw [hCR]; cmem 15)
  rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at hli15
  -- idx16 (base+64): BGEU x5, x6, +16 — NOT taken (b < 0xf8) → base+68
  have hbr16 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 16)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      ((bs.getD 0 0).zeroExtend 64) (0xf8 : Word) (base + 64))
  rw [show (base + 64 : Word) + signExtend13 (16 : BitVec 13) = base + 80 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 64 : Word) + 4 = base + 68 from by bv_omega] at hbr16
  have hnt16 := cpsBranchWithin_ntakenStripPure2 hbr16 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2
      (ult_zx_of_lt _ _ (by rw [show ((0xf8 : Word)).toNat = 248 from by decide]; exact h_hi)))
  -- idx17 (base+68): ADDI x10, x5, -192
  have ha17 := liftCode (cr' := CR)
    (addi_spec_gen_within .x10 .x5 ptr ((bs.getD 0 0).zeroExtend 64)
      (-192 : BitVec 12) (base + 68) (by decide))
    (by rw [hCR]; cmem 17)
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at ha17
  -- idx18 (base+72): ADDI x10, x10, 1
  have ha18 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x10
      (((bs.getD 0 0).zeroExtend 64) + signExtend12 (-192 : BitVec 12))
      (1 : BitVec 12) (base + 72) (by decide))
    (by rw [hCR]; cmem 18)
  rw [show (base + 72 : Word) + 4 = base + 76 from by bv_omega,
      ris_result_192 _ h_lo] at ha18
  -- idx19 (base+76): ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 76) raVal)
    (by rw [hCR]; cmem 19)
  -- frames
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hli
  have ht2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) ht2
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hli5
  have ht6F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) ht6
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hli10
  have ht11F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) ht11
  have hli15F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hli15
  have hnt16F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hnt16
  have ha17F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ (0xf8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs)
    (by pcf) ha17
  have ha18F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xf8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) ha18
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs.getD 0 0).toNat - 191)) **
     ((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xf8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion ptr bs)
    (by pcf) hret
  -- compose
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 ht2F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli5F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 ht6F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 hli10F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 ht11F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hli15F
  have hc8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc7 hnt16F
  have hc9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc8 ha17F
  have hc10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc9 ha18F
  have hc11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc10 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc11
  have hq1 : (((.x5 : Reg) ↦ᵣ ((bs.getD 0 0).zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0xf8 : Word)) **
       (((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs.getD 0 0).toNat - 191)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
  xperm_hyp hq2

/-! ## Pure bridges: the guest span IS `(encode item).length`

    For a successful `decode`, the head byte pins the full encoded span
    (`decode_eq_some_imp_encode` right-inverse + the per-class decoder
    characterization). -/

private theorem fuel_succ (n : Nat) : 2 * n + 2 = (2 * n + 1) + 1 := rfl

/-- Single-byte form: span 1. -/
theorem decode_span_singleByte (pfx : Byte) (rest0 : List Byte)
    (item : RLPItem) (rest : List Byte)
    (h : decode (pfx :: rest0) = some (item, rest))
    (hb : pfx.toNat < 0x80) :
    (encode item).length = 1 := by
  rw [decode_cons_eq_decodeAux_fuel, fuel_succ,
      decodeAux_single_byte _ _ _ hb] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hi, -⟩ := h
  subst hi
  simp [encode, encodeBytes, hb]

/-- Short-string form: span `pfx - 0x80 + 1 = pfx - 127`. -/
theorem decode_span_shortBytes (pfx : Byte) (rest0 : List Byte)
    (item : RLPItem) (rest : List Byte)
    (h : decode (pfx :: rest0) = some (item, rest))
    (hlo : 0x80 ≤ pfx.toNat) (hhi : pfx.toNat ≤ 0xB7) :
    (encode item).length = pfx.toNat - 127 := by
  have henc := decode_eq_some_imp_encode _ _ _ h
  have hcl : classifyPrefix pfx = .shortBytes :=
    (classifyPrefix_shortBytes_iff pfx).mpr ⟨hlo, hhi⟩
  rw [decode_cons_eq_decodeAux_fuel, fuel_succ,
      decodeAux_cons_shortBytes_of_classifyPrefix _ _ _ hcl] at h
  cases htk : takeBytes rest0 (rlpPrefixShortBytesPayloadLen pfx) with
  | none => rw [htk] at h; simp at h
  | some pair =>
    obtain ⟨data, rest'⟩ := pair
    obtain ⟨hsp, hpl⟩ := takeBytes_eq_some_imp htk
    rw [htk] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    have hrest : rest = rest' := by
      rcases data with _ | ⟨b, _ | ⟨c, t⟩⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm
      · replace h : (if b.toNat < 0x80 then none
            else some (RLPItem.bytes [b], rest')) = some (item, rest) := h
        by_cases hb : b.toNat < 0x80
        · rw [if_pos hb] at h; exact absurd h (by simp)
        · rw [if_neg hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm
    have hlenc := congrArg List.length henc
    have hlsp := congrArg List.length hsp
    rw [List.length_cons, List.length_append, hrest] at hlenc
    rw [List.length_append, hpl, rlpPrefixShortBytesPayloadLen] at hlsp
    omega

/-- Short-list form: span `pfx - 0xC0 + 1 = pfx - 191`. -/
theorem decode_span_shortList (pfx : Byte) (rest0 : List Byte)
    (item : RLPItem) (rest : List Byte)
    (h : decode (pfx :: rest0) = some (item, rest))
    (hlo : 0xC0 ≤ pfx.toNat) (hhi : pfx.toNat ≤ 0xF7) :
    (encode item).length = pfx.toNat - 191 := by
  have henc := decode_eq_some_imp_encode _ _ _ h
  have hcl : classifyPrefix pfx = .shortList :=
    (classifyPrefix_shortList_iff pfx).mpr ⟨hlo, hhi⟩
  rw [decode_cons_eq_decodeAux_fuel, fuel_succ,
      decodeAux_cons_shortList_of_classifyPrefix _ _ _ hcl] at h
  cases htk : takeBytes rest0 (rlpPrefixShortListPayloadLen pfx) with
  | none => rw [htk] at h; simp at h
  | some pair =>
    obtain ⟨payload, rest'⟩ := pair
    obtain ⟨hsp, hpl⟩ := takeBytes_eq_some_imp htk
    rw [htk] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases hdi : decodeItems (2 * rest0.length + 1) payload with
    | none => rw [hdi] at h; simp at h
    | some pair2 =>
      obtain ⟨items, leftover⟩ := pair2
      rw [hdi] at h
      simp only [Option.bind_some] at h
      cases leftover with
      | cons x xs => simp at h
      | nil =>
        replace h : some (RLPItem.list items, rest') = some (item, rest) := by
          simpa using h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have hrest : rest = rest' := h.2.symm
        have hlenc := congrArg List.length henc
        have hlsp := congrArg List.length hsp
        rw [List.length_cons, List.length_append, hrest] at hlenc
        rw [List.length_append, hpl, rlpPrefixShortListPayloadLen] at hlsp
        omega

/-! ## The unified account-path dispatch -/

/-- The head-byte forms covered by these triples (the full account path:
    scalar/short-string fields plus embedded short lists; long strings
    `0xb8..0xbf` and long lists `0xf8..` are excluded). -/
def SpanForm (b : BitVec 8) : Prop :=
  b.toNat < 0xb8 ∨ (0xc0 ≤ b.toNat ∧ b.toNat < 0xf8)

/-- The value the guest computes, per head byte. -/
def risSpan (b : BitVec 8) : Word :=
  if b.toNat < 0x80 then 1
  else if b.toNat < 0xb8 then BitVec.ofNat 64 (b.toNat - 127)
  else BitVec.ofNat 64 (b.toNat - 191)

/-- **The span bridge**: on a successful `decode` of a covered form, the
    guest's computed value is exactly the pure `(encode item).length`. -/
theorem risSpan_eq_encode_length (bs : List Byte) (item : RLPItem) (rest : List Byte)
    (h : decode bs = some (item, rest))
    (h_form : SpanForm (bs.getD 0 0)) :
    risSpan (bs.getD 0 0) = BitVec.ofNat 64 (encode item).length := by
  cases bs with
  | nil =>
    rw [decode_eq_decodeAux_length, decodeAux_nil] at h
    exact absurd h (by simp)
  | cons pfx rest0 =>
    simp only [List.getD_cons_zero] at h_form ⊢
    rcases h_form with hlt | ⟨hlo, hhi⟩
    · by_cases hb : pfx.toNat < 0x80
      · rw [decode_span_singleByte pfx rest0 item rest h hb]
        unfold risSpan
        rw [if_pos hb]
        decide
      · unfold risSpan
        rw [if_neg hb, if_pos hlt,
            decode_span_shortBytes pfx rest0 item rest h (by omega) (by omega)]
    · unfold risSpan
      rw [if_neg (by omega), if_neg (by omega),
          decode_span_shortList pfx rest0 item rest h hlo (by omega)]

/-- **`rlp_item_size`, unified account-path triple** (`∀ base`, scratch
    released): for any buffer whose head decodes successfully in a covered
    form, `a0` returns the full encoded byte span of the item —
    `(EL.RLP.encode item).length` — clobbering only `t0`/`t1`. -/
theorem rlp_item_size_form_own_spec_within (base ptr raVal : Word)
    (bs : List (BitVec 8)) (item : RLPItem) (rest : List Byte)
    (h_align : ptr.toNat % 8 = 0)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_decode : decode bs = some (item, rest))
    (h_form : SpanForm (bs.getD 0 0)) :
    cpsTripleWithin 12 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      ((((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) **
       regOwn .x5 ** regOwn .x6)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode item).length) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) := by
  have h_len : 0 < bs.length := by
    cases bs with
    | nil =>
      rw [decode_eq_decodeAux_length, decodeAux_nil] at h_decode
      exact absurd h_decode (by simp)
    | cons a l => simp
  rw [← risSpan_eq_encode_length bs item rest h_decode h_form]
  -- peel the scratch registers
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) ** regOwn .x5)
      (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) **
        ((.x6 : Reg) ↦ᵣ v6))
      (fun v5 => ?_))
  rcases h_form with hlt | ⟨hlo, hhi⟩
  · by_cases hb : (bs.getD 0 0).toNat < 0x80
    · rw [show risSpan (bs.getD 0 0) = (1 : Word) from by
          unfold risSpan; rw [if_pos hb]]
      exact cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (rlp_item_size_single_pinned_spec_within base ptr raVal v5 v6 bs
            h_align h_len h_valid hb))
    · rw [show risSpan (bs.getD 0 0) = BitVec.ofNat 64 ((bs.getD 0 0).toNat - 127) from by
          unfold risSpan; rw [if_neg hb, if_pos hlt]]
      exact cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (rlp_item_size_short_string_pinned_spec_within base ptr raVal v5 v6 bs
            h_align h_len h_valid (by omega) hlt))
  · rw [show risSpan (bs.getD 0 0) = BitVec.ofNat 64 ((bs.getD 0 0).toNat - 191) from by
        unfold risSpan; rw [if_neg (by omega), if_neg (by omega)]]
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
        (rlp_item_size_short_list_pinned_spec_within base ptr raVal v5 v6 bs
          h_align h_len h_valid hlo hhi))

/-! ## `rlp_item_size` at its linked guest address -/

/-- Guest entry of `rlp_item_size`. -/
def rlpItemSizeBase : Word := BitVec.ofNat 64 GuestAddrs.rlp_item_size

theorem rlpItemSizeBase_eq : rlpItemSizeBase = (0x80004d34 : Word) := by decide

/-- The `rlp_item_size` body at its linked guest address. -/
abbrev rlpItemSizeCode : CodeReq :=
  CodeReq.ofProg rlpItemSizeBase rlpItemSize_prog

/-- **`rlp_item_size` at its linked guest address** — the form the
    `rlp_item_span` / `mpt_splice_slot` compositions consume. -/
theorem rlp_item_size_spec_within (ptr raVal : Word)
    (bs : List (BitVec 8)) (item : RLPItem) (rest : List Byte)
    (h_align : ptr.toNat % 8 = 0)
    (h_valid : ∀ k, k < bs.length → isValidByteAccess (ptr + BitVec.ofNat 64 k) = true)
    (h_decode : decode bs = some (item, rest))
    (h_form : SpanForm (bs.getD 0 0)) :
    cpsTripleWithin 12 rlpItemSizeBase (raVal &&& ~~~1) rlpItemSizeCode
      ((((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) **
       regOwn .x5 ** regOwn .x6)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode item).length) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bs) :=
  rlp_item_size_form_own_spec_within rlpItemSizeBase ptr raVal bs item rest
    h_align h_valid h_decode h_form

/-! ## `rlp_encode_list_prefix` — per-form `∀ base` triples

    ABI (`RlpRead.lean`): `a0` = payload length, `a1` = output bytes ptr
    (caller supplies ≥ 9 bytes), `a2` = u64 out ptr (prefix byte
    length); returns `a0 = 0` (total function on the success paths). -/

/-- General `ult` from `toNat`. -/
private theorem ult_of_toNat_lt {a c : Word} (h : a.toNat < c.toNat) :
    BitVec.ult a c := by
  simpa [BitVec.ult, decide_eq_true_eq] using h

/-- General `¬ ult` from `toNat`. -/
private theorem not_ult_of_toNat_ge {a c : Word} (h : c.toNat ≤ a.toNat) :
    ¬ BitVec.ult a c := by
  simp only [BitVec.ult, decide_eq_true_eq]
  omega

/-- The short-form header byte: `truncate 8 (len + 192) = 0xC0 + len`. -/
private theorem relp_short_byte (len : Word) :
    (len + signExtend12 (192 : BitVec 12)).truncate 8
      = BitVec.ofNat 8 (0xC0 + len.toNat) := by
  have h192 : (signExtend12 (192 : BitVec 12) : Word).toNat = 192 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, h192, BitVec.toNat_ofNat]
  omega

/-- A word truncates to the byte of its `toNat`. -/
private theorem trunc8_eq_ofNat_toNat (len : Word) :
    len.truncate 8 = BitVec.ofNat 8 len.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- `x >>> ((0 : Word).toNat % 64) = x` (the single-length-byte SRL). -/
private theorem srl_zero (x : Word) : x >>> ((0 : Word).toNat % 64) = x := by
  rw [show ((0 : Word)).toNat % 64 = 0 from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  simp

/-- **`rlp_encode_list_prefix`, short form** (`len < 56`): writes the
    single header byte `0xC0 + len` and header length 1, returns `a0 = 0`;
    scratch registers pinned. -/
theorem rlp_encode_list_prefix_short_pinned_spec_within
    (base len outPtr cellPtr raVal v5 v6 v7 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len : len.toNat < 56)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 8 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpEncodeListPrefix_prog)
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
       (cellPtr ↦ₘ (1 : Word))) := by
  set CR := CodeReq.ofProg base rlpEncodeListPrefix_prog with hCR
  -- idx0 (base+0): LI x5, 56
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x5 v5 (56 : Word) base (by decide))
    (by rw [hCR]; cmem 0)
  -- idx1 (base+4): BGEU x10, x5, +28 — NOT taken (len < 56)
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 1)
    (h := bgeu_spec_gen_within .x10 .x5 (28 : BitVec 13) len (56 : Word) (base + 4))
  rw [show (base + 4 : Word) + signExtend13 (28 : BitVec 13) = base + 32 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbr
  have hult : BitVec.ult len (56 : Word) :=
    ult_of_toNat_lt (by rw [show ((56 : Word)).toNat = 56 from by decide]; exact h_len)
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult)
  -- idx2 (base+8): ADDI x6, x10, 192
  have ha2 := liftCode (cr' := CR)
    (addi_spec_gen_within .x6 .x10 v6 len (192 : BitVec 12) (base + 8) (by decide))
    (by rw [hCR]; cmem 2)
  rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at ha2
  -- idx3 (base+12): SB x11, x6 — out[0] := 0xC0 + len
  have hsb := liftCode (cr' := CR)
    (bytesRegion_sb_within .x11 .x6 outPtr (len + signExtend12 (192 : BitVec 12))
      (base + 12) outBytes 0 h_out_align h_out_len
      (by have := outPtr.isLt; omega) (h_out_valid 0 h_out_len))
    (by rw [hCR]; cmem 3)
  rw [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega,
      relp_short_byte len,
      show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hsb
  -- idx4 (base+16): LI x7, 1
  have hli7 := liftCode (cr' := CR)
    (li_spec_gen_within .x7 v7 (1 : Word) (base + 16) (by decide))
    (by rw [hCR]; cmem 4)
  rw [show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at hli7
  -- idx5 (base+20): SD x12, x7 — *cell := 1
  have hsd := liftCode (cr' := CR)
    (sd_spec_within .x12 .x7 cellPtr (1 : Word) cellOld (0 : BitVec 12) (base + 20))
    (by rw [hCR]; cmem 5)
  simp only [signExtend12_0] at hsd
  rw [show cellPtr + (0 : Word) = cellPtr from by bv_omega,
      show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hsd
  -- idx6 (base+24): LI x10, 0
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x10 len (0 : Word) (base + 24) (by decide))
    (by rw [hCR]; cmem 6)
  rw [show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hli10
  -- idx7 (base+28): ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 28) raVal)
    (by rw [hCR]; cmem 7)
  -- frames
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli5
  have hntF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt
  have ha2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha2
  have hsbF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (cellPtr ↦ₘ cellOld))
    (by pcf) hsb
  have hli7F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x6 : Reg) ↦ᵣ (len + signExtend12 (192 : BitVec 12))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
     (cellPtr ↦ₘ cellOld))
    (by pcf) hli7
  have hsdF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) ** ((.x11 : Reg) ↦ᵣ outPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x6 : Reg) ↦ᵣ (len + signExtend12 (192 : BitVec 12))) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))))
    (by pcf) hsd
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x6 : Reg) ↦ᵣ (len + signExtend12 (192 : BitVec 12))) **
     ((.x7 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
     (cellPtr ↦ₘ (1 : Word)))
    (by pcf) hli10
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
     ((.x12 : Reg) ↦ᵣ cellPtr) ** ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x6 : Reg) ↦ᵣ (len + signExtend12 (192 : BitVec 12))) **
     ((.x7 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
     (cellPtr ↦ₘ (1 : Word)))
    (by pcf) hret
  -- compose
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hli5F hntF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 ha2F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hsbF
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 hli7F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 hsdF
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 hli10F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc7
  have hq1 : (((.x5 : Reg) ↦ᵣ (56 : Word)) **
      (((.x6 : Reg) ↦ᵣ (len + signExtend12 (192 : BitVec 12))) **
       (((.x7 : Reg) ↦ᵣ (1 : Word)) **
        (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
         ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + len.toNat))) **
         (cellPtr ↦ₘ (1 : Word)))))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _)
      (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh))) h hq1
  xperm_hyp hq2

/-- **`rlp_encode_list_prefix`, 1-length-byte long form** (`56 ≤ len < 256`
    — the account list's form, cf. `encodeAccount_eq_cons`): writes the
    header bytes `[0xF8, len]` and header length 2, returns `a0 = 0`;
    scratch registers pinned.  On this path the guest clobbers
    `t0`/`t3`–`t6` (`x5`, `x28`–`x31`); `x6`/`x7` are untouched. -/
theorem rlp_encode_list_prefix_long1_pinned_spec_within
    (base len outPtr cellPtr raVal v5 v28 v29 v30 v31 : Word)
    (outBytes : List (BitVec 8)) (cellOld : Word)
    (h_len_lo : 56 ≤ len.toNat)
    (h_len_hi : len.toNat < 256)
    (h_out_align : outPtr.toNat % 8 = 0)
    (h_out_len : 1 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 22 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpEncodeListPrefix_prog)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
       regOwn .x5 ** regOwn .x28 ** regOwn .x29 **
       regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr
         ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
       (cellPtr ↦ₘ (2 : Word))) := by
  set CR := CodeReq.ofProg base rlpEncodeListPrefix_prog with hCR
  have h_out_len0 : 0 < outBytes.length := by omega
  -- idx0 (base+0): LI x5, 56
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x5 v5 (56 : Word) base (by decide))
    (by rw [hCR]; cmem 0)
  -- idx1 (base+4): BGEU x10, x5, +28 — TAKEN (len ≥ 56) → base+32
  have hbr1 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 1)
    (h := bgeu_spec_gen_within .x10 .x5 (28 : BitVec 13) len (56 : Word) (base + 4))
  rw [show (base + 4 : Word) + signExtend13 (28 : BitVec 13) = base + 32 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbr1
  have hnult56 : ¬ BitVec.ult len (56 : Word) :=
    not_ult_of_toNat_ge (by rw [show ((56 : Word)).toNat = 56 from by decide]; exact h_len_lo)
  have ht1 := cpsBranchWithin_takenStripPure2 hbr1 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact hnult56 ((sepConj_pure_right _).1 hQ).2)
  -- idx8 (base+32): LI x28, 1
  have hli28 := liftCode (cr' := CR)
    (li_spec_gen_within .x28 v28 (1 : Word) (base + 32) (by decide))
    (by rw [hCR]; cmem 8)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hli28
  -- idx9 (base+36): LI x29, 256
  have hli29 := liftCode (cr' := CR)
    (li_spec_gen_within .x29 v29 (256 : Word) (base + 36) (by decide))
    (by rw [hCR]; cmem 9)
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hli29
  -- idx10 (base+40): BLTU x10, x29, +80 — TAKEN (len < 256) → base+120
  have hbr10 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 10)
    (h := bltu_spec_gen_within .x10 .x29 (80 : BitVec 13) len (256 : Word) (base + 40))
  rw [show (base + 40 : Word) + signExtend13 (80 : BitVec 13) = base + 120 from by
        rw [show signExtend13 (80 : BitVec 13) = (80 : Word) from by decide]; bv_omega,
      show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hbr10
  have hult256 : BitVec.ult len (256 : Word) :=
    ult_of_toNat_lt (by rw [show ((256 : Word)).toNat = 256 from by decide]; exact h_len_hi)
  have ht10 := cpsBranchWithin_takenStripPure2 hbr10 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 hult256)
  -- idx30 (base+120): ADDI x29, x28, 247 — x29 := 0xF8
  have ha30 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x28 (256 : Word) (1 : Word)
      (247 : BitVec 12) (base + 120) (by decide))
    (by rw [hCR]; cmem 30)
  rw [show (base + 120 : Word) + 4 = base + 124 from by bv_omega,
      show (1 : Word) + signExtend12 (247 : BitVec 12) = (248 : Word) from by decide] at ha30
  -- idx31 (base+124): SB x11, x29 — out[0] := 0xF8
  have hsb31 := liftCode (cr' := CR)
    (bytesRegion_sb_within .x11 .x29 outPtr (248 : Word) (base + 124) outBytes 0
      h_out_align h_out_len0 (by have := outPtr.isLt; omega) (h_out_valid 0 h_out_len0))
    (by rw [hCR]; cmem 31)
  rw [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega,
      show ((248 : Word)).truncate 8 = (0xF8 : BitVec 8) from by decide,
      show (base + 124 : Word) + 4 = base + 128 from by bv_omega] at hsb31
  -- idx32 (base+128): MV x30, x11
  have hmv := liftCode (cr' := CR)
    (mv_spec_gen_within .x30 .x11 outPtr v30 (base + 128) (by decide))
    (by rw [hCR]; cmem 32)
  rw [show (base + 128 : Word) + 4 = base + 132 from by bv_omega] at hmv
  -- idx33 (base+132): ADDI x30, x30, 1
  have ha33 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x30 outPtr (1 : BitVec 12) (base + 132) (by decide))
    (by rw [hCR]; cmem 33)
  rw [show (base + 132 : Word) + 4 = base + 136 from by bv_omega,
      show outPtr + signExtend12 (1 : BitVec 12) = outPtr + BitVec.ofNat 64 1 from by
        rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]] at ha33
  -- idx34 (base+136): ADDI x29, x28, -1 — x29 := 0
  have ha34 := liftCode (cr' := CR)
    (addi_spec_gen_within .x29 .x28 (248 : Word) (1 : Word)
      (-1 : BitVec 12) (base + 136) (by decide))
    (by rw [hCR]; cmem 34)
  rw [show (base + 136 : Word) + 4 = base + 140 from by bv_omega,
      show (1 : Word) + signExtend12 (-1 : BitVec 12) = (0 : Word) from by decide] at ha34
  -- idx35 (base+140): BLT x29, x0, +28 — NOT taken (0 <ₛ 0 is false) → base+144
  have hbr35a := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 35)
    (h := blt_spec_gen_within .x29 .x0 (28 : BitVec 13) (0 : Word) (0 : Word) (base + 140))
  rw [show (base + 140 : Word) + signExtend13 (28 : BitVec 13) = base + 168 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 140 : Word) + 4 = base + 144 from by bv_omega] at hbr35a
  have hnt35 := cpsBranchWithin_ntakenStripPure2 hbr35a (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact (by decide : ¬ BitVec.slt (0 : Word) (0 : Word))
      ((sepConj_pure_right _).1 hQ).2)
  -- idx36 (base+144): SLLI x31, x29, 3 — x31 := 0
  have hsll := liftCode (cr' := CR)
    (slli_spec_gen_within .x31 .x29 v31 (0 : Word) (3 : BitVec 6) (base + 144) (by decide))
    (by rw [hCR]; cmem 36)
  rw [show (base + 144 : Word) + 4 = base + 148 from by bv_omega,
      show ((0 : Word) <<< ((3 : BitVec 6)).toNat) = (0 : Word) from by decide] at hsll
  -- idx37 (base+148): SRL x5, x10, x31 — x5 := len >> 0 = len
  have hsrl := liftCode (cr' := CR)
    (srl_spec_gen_within .x5 .x10 .x31 (56 : Word) len (0 : Word) (base + 148) (by decide))
    (by rw [hCR]; cmem 37)
  rw [show (base + 148 : Word) + 4 = base + 152 from by bv_omega, srl_zero len] at hsrl
  -- idx38 (base+152): SB x30, x5 — out[1] := len byte
  have hsb38 := liftCode (cr' := CR)
    (bytesRegion_sb_within .x30 .x5 outPtr len (base + 152)
      (outBytes.set 0 (0xF8 : BitVec 8)) 1
      h_out_align (by rw [List.length_set]; exact h_out_len)
      (by have := outPtr.isLt; omega) (h_out_valid 1 h_out_len))
    (by rw [hCR]; cmem 38)
  rw [trunc8_eq_ofNat_toNat len,
      show (base + 152 : Word) + 4 = base + 156 from by bv_omega] at hsb38
  -- idx39 (base+156): ADDI x30, x30, 1
  have ha39 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x30 (outPtr + BitVec.ofNat 64 1)
      (1 : BitVec 12) (base + 156) (by decide))
    (by rw [hCR]; cmem 39)
  rw [show (base + 156 : Word) + 4 = base + 160 from by bv_omega] at ha39
  -- idx40 (base+160): ADDI x29, x29, -1 — x29 := -1
  have ha40 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x29 (0 : Word) (-1 : BitVec 12) (base + 160) (by decide))
    (by rw [hCR]; cmem 40)
  rw [show (base + 160 : Word) + 4 = base + 164 from by bv_omega,
      show (0 : Word) + signExtend12 (-1 : BitVec 12)
        = (0xFFFFFFFFFFFFFFFF : Word) from by decide] at ha40
  -- idx41 (base+164): JAL x0, -24 — unconditional back-jump → base+140
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-24 : BitVec 21) (base + 164))
    (by rw [hCR]; cmem 41)
  rw [show (base + 164 : Word) + signExtend21 (-24 : BitVec 21) = base + 140 from by
        rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega] at hjal
  -- idx35 again (base+140): BLT x29, x0, +28 — TAKEN (-1 <ₛ 0) → base+168
  have hbr35b := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 35)
    (h := blt_spec_gen_within .x29 .x0 (28 : BitVec 13)
      (0xFFFFFFFFFFFFFFFF : Word) (0 : Word) (base + 140))
  rw [show (base + 140 : Word) + signExtend13 (28 : BitVec 13) = base + 168 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (base + 140 : Word) + 4 = base + 144 from by bv_omega] at hbr35b
  have ht35 := cpsBranchWithin_takenStripPure2 hbr35b (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2
      (by decide : BitVec.slt (0xFFFFFFFFFFFFFFFF : Word) (0 : Word)))
  -- idx42 (base+168): ADDI x30, x28, 1 — x30 := 2 (header length)
  have ha42 := liftCode (cr' := CR)
    (addi_spec_gen_within .x30 .x28
      ((outPtr + BitVec.ofNat 64 1) + signExtend12 (1 : BitVec 12)) (1 : Word)
      (1 : BitVec 12) (base + 168) (by decide))
    (by rw [hCR]; cmem 42)
  rw [show (base + 168 : Word) + 4 = base + 172 from by bv_omega,
      show (1 : Word) + signExtend12 (1 : BitVec 12) = (2 : Word) from by decide] at ha42
  -- idx43 (base+172): SD x12, x30 — *cell := 2
  have hsd := liftCode (cr' := CR)
    (sd_spec_within .x12 .x30 cellPtr (2 : Word) cellOld (0 : BitVec 12) (base + 172))
    (by rw [hCR]; cmem 43)
  simp only [signExtend12_0] at hsd
  rw [show cellPtr + (0 : Word) = cellPtr from by bv_omega,
      show (base + 172 : Word) + 4 = base + 176 from by bv_omega] at hsd
  -- idx44 (base+176): LI x10, 0
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x10 len (0 : Word) (base + 176) (by decide))
    (by rw [hCR]; cmem 44)
  rw [show (base + 176 : Word) + 4 = base + 180 from by bv_omega] at hli10
  -- idx45 (base+180): ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 180) raVal)
    (by rw [hCR]; cmem 45)
  -- frames
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli5
  have ht1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ht1
  have hli28F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli28
  have hli29F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) hli29
  have ht10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ht10
  have ha30F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr outBytes ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha30
  have hsb31F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsb31
  have hmvF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x29 : Reg) ↦ᵣ (248 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF8 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hmv
  have ha33F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x29 : Reg) ↦ᵣ (248 : Word)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF8 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha33
  have ha34F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF8 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) ha34
  have hnt35F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) ** ((.x31 : Reg) ↦ᵣ v31) **
     bytesRegion outPtr (outBytes.set 0 (0xF8 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hnt35
  have hsllF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ (56 : Word)) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF8 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsll
  have hsrlF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
     ((.x30 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr (outBytes.set 0 (0xF8 : BitVec 8)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsrl
  have hsb38F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x29 : Reg) ↦ᵣ (0 : Word)) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (cellPtr ↦ₘ cellOld))
    (by pcf) hsb38
  have ha39F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0 : Word)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ cellOld))
    (by pcf) ha39
  have ha40F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ ((outPtr + BitVec.ofNat 64 1) + signExtend12 (1 : BitVec 12))) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ cellOld))
    (by pcf) ha40
  have hjalF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x30 : Reg) ↦ᵣ ((outPtr + BitVec.ofNat 64 1) + signExtend12 (1 : BitVec 12))) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ cellOld))
    (by pcf) hjal
  rw [sepConj_emp_left'] at hjalF
  have ht35F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x30 : Reg) ↦ᵣ ((outPtr + BitVec.ofNat 64 1) + signExtend12 (1 : BitVec 12))) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ cellOld))
    (by pcf) ht35
  have ha42F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ cellOld))
    (by pcf) ha42
  have hsdF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ len) **
     ((.x11 : Reg) ↦ᵣ outPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)))
    (by pcf) hsd
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x30 : Reg) ↦ᵣ (2 : Word)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ (2 : Word)))
    (by pcf) hli10
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ outPtr) **
     ((.x12 : Reg) ↦ᵣ cellPtr) **
     ((.x5 : Reg) ↦ᵣ len) ** ((.x28 : Reg) ↦ᵣ (1 : Word)) **
     ((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
     ((.x30 : Reg) ↦ᵣ (2 : Word)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion outPtr
       ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
     (cellPtr ↦ₘ (2 : Word)))
    (by pcf) hret
  -- compose
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hli5F ht1F
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hli28F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli29F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 ht10F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 ha30F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 hsb31F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hmvF
  have hc8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc7 ha33F
  have hc9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc8 ha34F
  have hc10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc9 hnt35F
  have hc11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc10 hsllF
  have hc12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc11 hsrlF
  have hc13 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc12 hsb38F
  have hc14 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc13 ha39F
  have hc15 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc14 ha40F
  have hc16 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc15 hjalF
  have hc17 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc16 ht35F
  have hc18 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc17 ha42F
  have hc19 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc18 hsdF
  have hc20 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc19 hli10F
  have hc21 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc20 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc21
  have hq1 : (((.x5 : Reg) ↦ᵣ len) **
      (((.x28 : Reg) ↦ᵣ (1 : Word)) **
       (((.x29 : Reg) ↦ᵣ (0xFFFFFFFFFFFFFFFF : Word)) **
        (((.x30 : Reg) ↦ᵣ (2 : Word)) **
         (((.x31 : Reg) ↦ᵣ (0 : Word)) **
          (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
           ((.x11 : Reg) ↦ᵣ outPtr) ** ((.x12 : Reg) ↦ᵣ cellPtr) **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion outPtr
             ((outBytes.set 0 (0xF8 : BitVec 8)).set 1 (BitVec.ofNat 8 len.toNat)) **
           (cellPtr ↦ₘ (2 : Word)))))))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (sepConj_mono (regIs_to_regOwn .x30 _)
          (sepConj_mono (regIs_to_regOwn .x31 _) (fun _ hh => hh))))) h hq1
  xperm_hyp hq2

end RlpSpliceHelperSpec

end EvmAsm.Codegen
