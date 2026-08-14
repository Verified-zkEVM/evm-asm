/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecBodyLate

  Body phases for K145 `tx_signing_hash`: prefix/segs/kss setup + early glue.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecBodyEarly
import EvmAsm.Rv64.SAsm.AbiFrameOwn

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashResidual
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef
open EvmAsm.Rv64.Tactics

/-! ## Body: payload length + prefix-arg setup (`H+164 → H+216`)

    After successful nth: reload off/len from scratch, compute
    `payloadLen := (off + itemLen) - hdrLen`, then materialize prefix
    out/cell pointers and JAL `rlp_encode_list_prefix`. -/

abbrev tshPrefixOutPtr : Word := TshBuf + 16
abbrev tshPrefixCellPtr : Word := TshBuf + 80

theorem tsh_la_payload_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164) =
      Rv64.laHi (H + 164) TshBuf := by
  decide

theorem tsh_la_payload_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 164) =
      Rv64.laLo (H + 164) TshBuf := by
  decide

theorem tsh_la_payload_range : laInRange (H + 164) TshBuf := by
  decide

/-- `la t0, tsh_buf`. `H+164 → H+172`. -/
theorem tshPayloadLa_spec (v5 : Word) :
    cpsTripleWithin 2 (H + 164) (H + 172) fullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ TshBuf) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 164)
        (.AUIPC .x5 (Rv64.laHi (H + 164) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 164) 41
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 164)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_payload_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 164) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo (H + 164) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 168) 42
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 164)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 164 : Word) + 4 = H + 168 := by decide
    rw [hpc, ← tsh_la_payload_lo] at hi
    exact hmem a i hi
  have h := la_materialize_within .x5 v5 (H + 164) TshBuf
    (by decide) tsh_la_payload_range hau had
  rwa [show (H + 164 : Word) + 8 = H + 172 from by decide] at h

/-- `ld t1, 64(t0)` — nth item offset. `H+172 → H+176`. -/
theorem tshPayloadLdOff_spec (v6 offVal : Word) :
    cpsTripleWithin 1 (H + 172) (H + 176) fullCode
      ((.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ v6) ** (tshNthOffPtr ↦ₘ offVal))
      ((.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ offVal) ** (tshNthOffPtr ↦ₘ offVal)) := by
  have h0 := ld_spec_gen_within .x6 .x5 TshBuf v6 offVal (64 : BitVec 12) (H + 172)
    (by decide)
  rw [show (H + 172 : Word) + 4 = H + 176 from by decide,
      show TshBuf + signExtend12 (64 : BitVec 12) = tshNthOffPtr from by
        unfold tshNthOffPtr TshBuf; decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 172) 43
      (.LD .x6 .x5 (64 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- `ld t2, 72(t0)` — nth item length. `H+176 → H+180`. -/
theorem tshPayloadLdLen_spec (v7 lenVal : Word) :
    cpsTripleWithin 1 (H + 176) (H + 180) fullCode
      ((.x5 ↦ᵣ TshBuf) ** (.x7 ↦ᵣ v7) ** (tshNthLenPtr ↦ₘ lenVal))
      ((.x5 ↦ᵣ TshBuf) ** (.x7 ↦ᵣ lenVal) ** (tshNthLenPtr ↦ₘ lenVal)) := by
  have h0 := ld_spec_gen_within .x7 .x5 TshBuf v7 lenVal (72 : BitVec 12) (H + 176)
    (by decide)
  rw [show (H + 176 : Word) + 4 = H + 180 from by decide,
      show TshBuf + signExtend12 (72 : BitVec 12) = tshNthLenPtr from by
        unfold tshNthLenPtr TshBuf; decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 176) 44
      (.LD .x7 .x5 (72 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- `add t1, t1, t2`. `H+180 → H+184`. -/
theorem tshPayloadAdd_spec (offVal lenVal : Word) :
    cpsTripleWithin 1 (H + 180) (H + 184) fullCode
      ((.x6 ↦ᵣ offVal) ** (.x7 ↦ᵣ lenVal))
      ((.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal)) := by
  have h0 := add_spec_gen_rd_eq_rs1_within .x6 .x7 offVal lenVal (H + 180) (by decide)
  rw [show (H + 180 : Word) + 4 = H + 184 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 180) 45
      (.ADD .x6 .x6 .x7)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- `sub s6, t1, s5` — payload length. `H+184 → H+188`. -/
theorem tshPayloadSub_spec (endOff hdrLen v22 : Word) :
    cpsTripleWithin 1 (H + 184) (H + 188) fullCode
      ((.x6 ↦ᵣ endOff) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22))
      ((.x6 ↦ᵣ endOff) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ (endOff - hdrLen))) := by
  have h0 := sub_spec_gen_within .x22 .x6 .x21 endOff hdrLen v22 (H + 184) (by decide)
  rw [show (H + 184 : Word) + 4 = H + 188 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 184) 46
      (.SUB .x22 .x6 .x21)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- `mv a0, s6`. `H+188 → H+192`. -/
theorem tshPrefixArg0_spec (payloadLen v10 : Word) :
    cpsTripleWithin 1 (H + 188) (H + 192) fullCode
      ((.x22 ↦ᵣ payloadLen) ** (.x10 ↦ᵣ v10))
      ((.x22 ↦ᵣ payloadLen) ** (.x10 ↦ᵣ payloadLen)) := by
  have h0 := mv_spec_gen_within .x10 .x22 payloadLen v10 (H + 188) (by decide)
  rw [show (H + 188 : Word) + 4 = H + 192 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 188) 47
      (.MV .x10 .x22)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- Load off/len and compute payloadLen into `s6`/`a0`. `H+164 → H+192`. -/
theorem tshPayloadLen_spec
    (v5 v6 v7 v10 v22 offVal lenVal hdrLen : Word) :
    cpsTripleWithin 8 (H + 164) (H + 192) fullCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal))
      ((.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
        (.x10 ↦ᵣ ((offVal + lenVal) - hdrLen)) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ ((offVal + lenVal) - hdrLen)) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal)) := by
  have hla := tshPayloadLa_spec v5
  have hlaF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ hdrLen) **
      (.x22 ↦ᵣ v22) ** (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal))
    (by pcf) hla
  have hld0 := tshPayloadLdOff_spec v6 offVal
  have hld0F := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
      (tshNthLenPtr ↦ₘ lenVal)) (by pcf) hld0
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlaF hld0F
  have hld1 := tshPayloadLdLen_spec v7 lenVal
  have hld1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ offVal) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
      (tshNthOffPtr ↦ₘ offVal)) (by pcf) hld1
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hld1F
  have hadd := tshPayloadAdd_spec offVal lenVal
  have haddF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ TshBuf) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal)) (by pcf) hadd
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c012 haddF
  have hsub := tshPayloadSub_spec (offVal + lenVal) hdrLen v22
  have hsubF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ TshBuf) ** (.x7 ↦ᵣ lenVal) ** (.x10 ↦ᵣ v10) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal)) (by pcf) hsub
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c0123 hsubF
  have hmv := tshPrefixArg0_spec ((offVal + lenVal) - hdrLen) v10
  have hmvF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
      (.x21 ↦ᵣ hdrLen) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal)) (by pcf) hmv
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01234 hmvF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

/-! ## Body: prefix out/cell pointer materialization (`H+192 → H+216`) -/

theorem tsh_la_prefix_out_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192) =
      Rv64.laHi (H + 192) TshBuf := by
  decide

theorem tsh_la_prefix_out_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 192) =
      Rv64.laLo (H + 192) TshBuf := by
  decide

theorem tsh_la_prefix_out_range : laInRange (H + 192) TshBuf := by
  decide

theorem tsh_la_prefix_cell_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204) =
      Rv64.laHi (H + 204) TshBuf := by
  decide

theorem tsh_la_prefix_cell_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 204) =
      Rv64.laLo (H + 204) TshBuf := by
  decide

theorem tsh_la_prefix_cell_range : laInRange (H + 204) TshBuf := by
  decide

/-- `la a1, tsh_buf; addi a1, a1, 16` → `tshPrefixOutPtr`. `H+192 → H+204`. -/
theorem tshPrefixOutPtr_spec (v11 : Word) :
    cpsTripleWithin 3 (H + 192) (H + 204) fullCode
      (.x11 ↦ᵣ v11) (.x11 ↦ᵣ tshPrefixOutPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 192)
        (.AUIPC .x11 (Rv64.laHi (H + 192) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 192) 48
      (.AUIPC .x11 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 192)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_prefix_out_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 192) + 4)
        (.ADDI .x11 .x11 (Rv64.laLo (H + 192) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 196) 49
      (.ADDI .x11 .x11 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 192)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 192 : Word) + 4 = H + 196 := by decide
    rw [hpc, ← tsh_la_prefix_out_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x11 v11 (H + 192) TshBuf
    (by decide) tsh_la_prefix_out_range hau had
  rw [show (H + 192 : Word) + 8 = H + 200 from by decide] at hla
  have haddi := addi_spec_gen_same_within .x11 TshBuf (16 : BitVec 12) (H + 200)
    (by decide)
  rw [show (H + 200 : Word) + 4 = H + 204 from by decide,
      show TshBuf + signExtend12 (16 : BitVec 12) = tshPrefixOutPtr from by
        unfold tshPrefixOutPtr TshBuf; decide] at haddi
  have laddi := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 200) 50
      (.ADDI .x11 .x11 (16 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) haddi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr hla laddi)

/-- `la a2, tsh_buf; addi a2, a2, 80` → `tshPrefixCellPtr`. `H+204 → H+216`. -/
theorem tshPrefixCellPtr_spec (v12 : Word) :
    cpsTripleWithin 3 (H + 204) (H + 216) fullCode
      (.x12 ↦ᵣ v12) (.x12 ↦ᵣ tshPrefixCellPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 204)
        (.AUIPC .x12 (Rv64.laHi (H + 204) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 204) 51
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 204)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_prefix_cell_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 204) + 4)
        (.ADDI .x12 .x12 (Rv64.laLo (H + 204) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 208) 52
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 204)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 204 : Word) + 4 = H + 208 := by decide
    rw [hpc, ← tsh_la_prefix_cell_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x12 v12 (H + 204) TshBuf
    (by decide) tsh_la_prefix_cell_range hau had
  rw [show (H + 204 : Word) + 8 = H + 212 from by decide] at hla
  have haddi := addi_spec_gen_same_within .x12 TshBuf (80 : BitVec 12) (H + 212)
    (by decide)
  rw [show (H + 212 : Word) + 4 = H + 216 from by decide,
      show TshBuf + signExtend12 (80 : BitVec 12) = tshPrefixCellPtr from by
        unfold tshPrefixCellPtr TshBuf; decide] at haddi
  have laddi := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 212) 53
      (.ADDI .x12 .x12 (80 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) haddi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr hla laddi)

/-- Combined prefix arg pointers. `H+192 → H+216`. -/
theorem tshPrefixPtrs_spec (v11 v12 : Word) :
    cpsTripleWithin (3 + 3) (H + 192) (H + 216) fullCode
      ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr)) := by
  have h1 := tshPrefixOutPtr_spec v11
  have h1F := cpsTripleWithin_frameR (.x12 ↦ᵣ v12) (by pcf) h1
  have h1W : cpsTripleWithin 3 (H + 192) (H + 204) fullCode
      ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x12 ↦ᵣ v12) ** (.x11 ↦ᵣ tshPrefixOutPtr)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have h2 := tshPrefixCellPtr_spec v12
  have h2F := cpsTripleWithin_frameR (.x11 ↦ᵣ tshPrefixOutPtr) (by pcf) h2
  have h2W : cpsTripleWithin 3 (H + 204) (H + 216) fullCode
      ((.x12 ↦ᵣ v12) ** (.x11 ↦ᵣ tshPrefixOutPtr))
      ((.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_same_cr h1W h2W

/-! ## Body: post-prefix segment-table base (`H+220 → H+244`)

    Reload prefix-written length from `tsh_buf+80`, materialize the
    3-segment descriptor table at `tsh_buf+128`. -/

abbrev tshSegsBase : Word := TshBuf + 128

theorem tsh_la_post_prefix_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220) =
      Rv64.laHi (H + 220) TshBuf := by
  decide

theorem tsh_la_post_prefix_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 220) =
      Rv64.laLo (H + 220) TshBuf := by
  decide

theorem tsh_la_post_prefix_range : laInRange (H + 220) TshBuf := by
  decide

theorem tsh_la_segs_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232) =
      Rv64.laHi (H + 232) TshBuf := by
  decide

theorem tsh_la_segs_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 232) =
      Rv64.laLo (H + 232) TshBuf := by
  decide

theorem tsh_la_segs_range : laInRange (H + 232) TshBuf := by
  decide

/-- `la t0, tsh_buf`. `H+220 → H+228`. -/
theorem tshPostPrefixLa_spec (v5 : Word) :
    cpsTripleWithin 2 (H + 220) (H + 228) fullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ TshBuf) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 220)
        (.AUIPC .x5 (Rv64.laHi (H + 220) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 220) 55
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 220)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_post_prefix_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 220) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo (H + 220) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 224) 56
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 220)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 220 : Word) + 4 = H + 224 := by decide
    rw [hpc, ← tsh_la_post_prefix_lo] at hi
    exact hmem a i hi
  have h := la_materialize_within .x5 v5 (H + 220) TshBuf
    (by decide) tsh_la_post_prefix_range hau had
  rwa [show (H + 220 : Word) + 8 = H + 228 from by decide] at h

/-- `ld t4, 80(t0)` — prefix byte-count cell. `H+228 → H+232`. -/
theorem tshPostPrefixLdCell_spec (v29 cellVal : Word) :
    cpsTripleWithin 1 (H + 228) (H + 232) fullCode
      ((.x5 ↦ᵣ TshBuf) ** (.x29 ↦ᵣ v29) ** (tshPrefixCellPtr ↦ₘ cellVal))
      ((.x5 ↦ᵣ TshBuf) ** (.x29 ↦ᵣ cellVal) ** (tshPrefixCellPtr ↦ₘ cellVal)) := by
  have h0 := ld_spec_gen_within .x29 .x5 TshBuf v29 cellVal (80 : BitVec 12) (H + 228)
    (by decide)
  rw [show (H + 228 : Word) + 4 = H + 232 from by decide,
      show TshBuf + signExtend12 (80 : BitVec 12) = tshPrefixCellPtr from by
        unfold tshPrefixCellPtr TshBuf; decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 228) 57
      (.LD .x29 .x5 (80 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- `la t5, tsh_buf; addi t5, t5, 128` → `tshSegsBase`. `H+232 → H+244`. -/
theorem tshSegsBase_spec (v30 : Word) :
    cpsTripleWithin 3 (H + 232) (H + 244) fullCode
      (.x30 ↦ᵣ v30) (.x30 ↦ᵣ tshSegsBase) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 232)
        (.AUIPC .x30 (Rv64.laHi (H + 232) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 232) 58
      (.AUIPC .x30 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 232)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_segs_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 232) + 4)
        (.ADDI .x30 .x30 (Rv64.laLo (H + 232) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 236) 59
      (.ADDI .x30 .x30 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 232)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 232 : Word) + 4 = H + 236 := by decide
    rw [hpc, ← tsh_la_segs_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x30 v30 (H + 232) TshBuf
    (by decide) tsh_la_segs_range hau had
  rw [show (H + 232 : Word) + 8 = H + 240 from by decide] at hla
  have haddi := addi_spec_gen_same_within .x30 TshBuf (128 : BitVec 12) (H + 240)
    (by decide)
  rw [show (H + 240 : Word) + 4 = H + 244 from by decide,
      show TshBuf + signExtend12 (128 : BitVec 12) = tshSegsBase from by
        unfold tshSegsBase TshBuf; decide] at haddi
  have laddi := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 240) 60
      (.ADDI .x30 .x30 (128 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) haddi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr hla laddi)

/-- Cell reload + segs base. `H+220 → H+244`. -/
theorem tshPostPrefixSegsPrep_spec (v5 v29 v30 cellVal : Word) :
    cpsTripleWithin 6 (H + 220) (H + 244) fullCode
      ((.x5 ↦ᵣ v5) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (tshPrefixCellPtr ↦ₘ cellVal))
      ((.x5 ↦ᵣ TshBuf) ** (.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
        (tshPrefixCellPtr ↦ₘ cellVal)) := by
  have hla := tshPostPrefixLa_spec v5
  have hlaF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (tshPrefixCellPtr ↦ₘ cellVal))
    (by pcf) hla
  have hld := tshPostPrefixLdCell_spec v29 cellVal
  have hldF := cpsTripleWithin_frameR (.x30 ↦ᵣ v30) (by pcf) hld
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlaF hldF
  have hsegs := tshSegsBase_spec v30
  have hsegsF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ TshBuf) ** (.x29 ↦ᵣ cellVal) ** (tshPrefixCellPtr ↦ₘ cellVal))
    (by pcf) hsegs
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hsegsF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

/-! ## Body: fill 3-segment gather table + kss args (`H+244 → H+316`)

    Seg0 = optional type-prefix byte at `tsh_buf`; seg1 = short list
    prefix at `tsh_buf+16`; seg2 = RLP payload at `inPtr+hdrLen`. -/

/-- `li t0, 0`. `H+244 → H+248`. -/
theorem tshTypeLenLi0_spec (v5 : Word) :
    cpsTripleWithin 1 (H + 244) (H + 248) fullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x5 v5 (0 : Word) (H + 244) (by decide)
  rw [show (H + 244 : Word) + 4 = H + 248 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 244) 61
      (.LI .x5 (0 : Word))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

abbrev tshTypeLenBeqOff : BitVec 13 := (8 : BitVec 13)

theorem tshTypeLenBeq_taken_pc :
    (H + 248) + signExtend13 tshTypeLenBeqOff = H + 256 := by
  unfold tshTypeLenBeqOff H; decide

/-- `typePrefix = 0`: skip `li 1`, keep len 0. `H+248 → H+256`. -/
theorem tshTypeLenBeq_taken (tp : Word) (hz : tp = 0) :
    cpsTripleWithin 1 (H + 248) (H + 256) fullCode
      ((.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x19 .x0 tshTypeLenBeqOff tp 0 (H + 248)
  rw [tshTypeLenBeq_taken_pc] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 248) 62
        (.BEQ .x19 .x0 tshTypeLenBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbeq)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hz)

/-- `typePrefix ≠ 0`: fall through. `H+248 → H+252`. -/
theorem tshTypeLenBeq_ntaken (tp : Word) (hnz : tp ≠ 0) :
    cpsTripleWithin 1 (H + 248) (H + 252) fullCode
      ((.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x19 .x0 tshTypeLenBeqOff tp 0 (H + 248)
  rw [show (H + 248 : Word) + 4 = H + 252 from by decide] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 248) 62
        (.BEQ .x19 .x0 tshTypeLenBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbeq)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hnz ((sepConj_pure_right _).1 hBP).2)

/-- `li t0, 1`. `H+252 → H+256`. -/
theorem tshTypeLenLi1_spec (v5 : Word) :
    cpsTripleWithin 1 (H + 252) (H + 256) fullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x5 v5 (1 : Word) (H + 252) (by decide)
  rw [show (H + 252 : Word) + 4 = H + 256 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 252) 63
      (.LI .x5 (1 : Word))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- Typed path: `typePrefix ≠ 0` ⇒ `t0 := 1` at `H+256`. `H+244 → H+256`. -/
theorem tshTypeLenTyped_spec (tp v5 : Word) (hnz : tp ≠ 0) :
    cpsTripleWithin (1 + 1 + 1) (H + 244) (H + 256) fullCode
      ((.x5 ↦ᵣ v5) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (1 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := tshTypeLenLi0_spec v5
  have h0F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) h0
  have h0W : cpsTripleWithin 1 (H + 244) (H + 248) fullCode
      ((.x5 ↦ᵣ v5) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := tshTypeLenBeq_ntaken tp hnz
  have h1F := cpsTripleWithin_frameR (.x5 ↦ᵣ (0 : Word)) (by pcf) h1
  have h1W : cpsTripleWithin 1 (H + 248) (H + 252) fullCode
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have c01 := cpsTripleWithin_seq_same_cr h0W h1W
  have h2 := tshTypeLenLi1_spec (0 : Word)
  have h2F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) h2
  have h2W : cpsTripleWithin 1 (H + 252) (H + 256) fullCode
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (1 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_same_cr c01 h2W

/-- Untyped path: `typePrefix = 0` ⇒ `t0 := 0` at `H+256`. `H+244 → H+256`. -/
theorem tshTypeLenUntyped_spec (tp v5 : Word) (hz : tp = 0) :
    cpsTripleWithin (1 + 1) (H + 244) (H + 256) fullCode
      ((.x5 ↦ᵣ v5) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
  have h0 := tshTypeLenLi0_spec v5
  have h0F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) h0
  have h0W : cpsTripleWithin 1 (H + 244) (H + 248) fullCode
      ((.x5 ↦ᵣ v5) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := tshTypeLenBeq_taken tp hz
  have h1F := cpsTripleWithin_frameR (.x5 ↦ᵣ (0 : Word)) (by pcf) h1
  have h1W : cpsTripleWithin 1 (H + 248) (H + 256) fullCode
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ tp) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  exact cpsTripleWithin_seq_same_cr h0W h1W

theorem tsh_la_seg0_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256) =
      Rv64.laHi (H + 256) TshBuf := by
  decide

theorem tsh_la_seg0_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 256) =
      Rv64.laLo (H + 256) TshBuf := by
  decide

theorem tsh_la_seg0_range : laInRange (H + 256) TshBuf := by
  decide

/-- `la t6, tsh_buf` for seg0 ptr. `H+256 → H+264`. -/
theorem tshSeg0PtrLa_spec (v31 : Word) :
    cpsTripleWithin 2 (H + 256) (H + 264) fullCode
      (.x31 ↦ᵣ v31) (.x31 ↦ᵣ TshBuf) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 256)
        (.AUIPC .x31 (Rv64.laHi (H + 256) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 256) 64
      (.AUIPC .x31 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 256)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_seg0_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 256) + 4)
        (.ADDI .x31 .x31 (Rv64.laLo (H + 256) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 260) 65
      (.ADDI .x31 .x31 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 256)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 256 : Word) + 4 = H + 260 := by decide
    rw [hpc, ← tsh_la_seg0_lo] at hi
    exact hmem a i hi
  have h := la_materialize_within .x31 v31 (H + 256) TshBuf
    (by decide) tsh_la_seg0_range hau had
  rwa [show (H + 256 : Word) + 8 = H + 264 from by decide] at h

/-- Store seg0 `{ptr=tsh_buf, len=typeLen}`. `H+264 → H+272`. -/
theorem tshSeg0Store_spec (typeLen old0 old1 : Word) :
    cpsTripleWithin 2 (H + 264) (H + 272) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ typeLen)) := by
  have h0 := sd_spec_gen_within .x30 .x31 tshSegsBase TshBuf old0
    (0 : BitVec 12) (H + 264)
  rw [show (H + 264 : Word) + 4 = H + 268 from by decide,
      show tshSegsBase + signExtend12 (0 : BitVec 12) = tshSegsBase from by
        decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 264) 66
      (.SD .x30 .x31 (0 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0
  have c0 : cpsTripleWithin 1 (H + 264) (H + 268) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ old1)) := by
    have hF := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ typeLen) ** ((tshSegsBase + 8) ↦ₘ old1)) (by pcf) l0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1 := sd_spec_gen_within .x30 .x5 tshSegsBase typeLen old1
    (8 : BitVec 12) (H + 268)
  rw [show (H + 268 : Word) + 4 = H + 272 from by decide,
      show tshSegsBase + signExtend12 (8 : BitVec 12) = tshSegsBase + 8 from by
        decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 268) 67
      (.SD .x30 .x5 (8 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h1
  have c1 : cpsTripleWithin 1 (H + 268) (H + 272) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ old1))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ typeLen)) := by
    have hF := cpsTripleWithin_frameR
      ((.x31 ↦ᵣ TshBuf) ** (tshSegsBase ↦ₘ TshBuf)) (by pcf) l1
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- Seg0 ptr la + store. `H+256 → H+272`. -/
theorem tshSeg0Fill_spec (v31 typeLen old0 old1 : Word) :
    cpsTripleWithin (2 + 2) (H + 256) (H + 272) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ v31) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ typeLen)) := by
  have hla := tshSeg0PtrLa_spec v31
  have hlaF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ tshSegsBase) ** (.x5 ↦ᵣ typeLen) **
      (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1)) (by pcf) hla
  have hlaW : cpsTripleWithin 2 (H + 256) (H + 264) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ v31) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ TshBuf) ** (.x5 ↦ᵣ typeLen) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlaF
  have hsd := tshSeg0Store_spec typeLen old0 old1
  exact cpsTripleWithin_seq_same_cr hlaW hsd

/-! ## Body: seg1/seg2 stores + kss ABI args (`H+272 → H+316`) -/

theorem tsh_la_seg1_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272) =
      Rv64.laHi (H + 272) TshBuf := by
  decide

theorem tsh_la_seg1_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 272) =
      Rv64.laLo (H + 272) TshBuf := by
  decide

theorem tsh_la_seg1_range : laInRange (H + 272) TshBuf := by
  decide

/-- `la t6, tsh_buf; addi t6, t6, 16` → prefix-out ptr. `H+272 → H+284`. -/
theorem tshSeg1Ptr_spec (v31 : Word) :
    cpsTripleWithin 3 (H + 272) (H + 284) fullCode
      (.x31 ↦ᵣ v31) (.x31 ↦ᵣ tshPrefixOutPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 272)
        (.AUIPC .x31 (Rv64.laHi (H + 272) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 272) 68
      (.AUIPC .x31 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 272)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_seg1_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 272) + 4)
        (.ADDI .x31 .x31 (Rv64.laLo (H + 272) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 276) 69
      (.ADDI .x31 .x31 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 272)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 272 : Word) + 4 = H + 276 := by decide
    rw [hpc, ← tsh_la_seg1_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x31 v31 (H + 272) TshBuf
    (by decide) tsh_la_seg1_range hau had
  rw [show (H + 272 : Word) + 8 = H + 280 from by decide] at hla
  have haddi := addi_spec_gen_same_within .x31 TshBuf (16 : BitVec 12) (H + 280)
    (by decide)
  rw [show (H + 280 : Word) + 4 = H + 284 from by decide,
      show TshBuf + signExtend12 (16 : BitVec 12) = tshPrefixOutPtr from by
        unfold tshPrefixOutPtr TshBuf; decide] at haddi
  have laddi := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 280) 70
      (.ADDI .x31 .x31 (16 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) haddi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr hla laddi)

/-- Store seg1 `{ptr=prefixOut, len=cellVal}`. `H+284 → H+292`. -/
theorem tshSeg1Store_spec (cellVal old2 old3 : Word) :
    cpsTripleWithin 2 (H + 284) (H + 292) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ cellVal)) := by
  have h0 := sd_spec_gen_within .x30 .x31 tshSegsBase tshPrefixOutPtr old2
    (16 : BitVec 12) (H + 284)
  rw [show (H + 284 : Word) + 4 = H + 288 from by decide,
      show tshSegsBase + signExtend12 (16 : BitVec 12) = tshSegsBase + 16 from by
        decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 284) 71
      (.SD .x30 .x31 (16 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0
  have c0 : cpsTripleWithin 1 (H + 284) (H + 288) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ old3)) := by
    have hF := cpsTripleWithin_frameR
      ((.x29 ↦ᵣ cellVal) ** ((tshSegsBase + 24) ↦ₘ old3)) (by pcf) l0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1 := sd_spec_gen_within .x30 .x29 tshSegsBase cellVal old3
    (24 : BitVec 12) (H + 288)
  rw [show (H + 288 : Word) + 4 = H + 292 from by decide,
      show tshSegsBase + signExtend12 (24 : BitVec 12) = tshSegsBase + 24 from by
        decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 288) 72
      (.SD .x30 .x29 (24 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h1
  have c1 : cpsTripleWithin 1 (H + 288) (H + 292) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ old3))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ cellVal)) := by
    have hF := cpsTripleWithin_frameR
      ((.x31 ↦ᵣ tshPrefixOutPtr) ** ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr))
      (by pcf) l1
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- Seg1 ptr + store. `H+272 → H+292`. -/
theorem tshSeg1Fill_spec (v31 cellVal old2 old3 : Word) :
    cpsTripleWithin (3 + 2) (H + 272) (H + 292) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ v31) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ cellVal)) := by
  have hla := tshSeg1Ptr_spec v31
  have hlaF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ tshSegsBase) ** (.x29 ↦ᵣ cellVal) **
      ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3)) (by pcf) hla
  have hlaW : cpsTripleWithin 3 (H + 272) (H + 284) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ v31) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ tshPrefixOutPtr) ** (.x29 ↦ᵣ cellVal) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlaF
  exact cpsTripleWithin_seq_same_cr hlaW (tshSeg1Store_spec cellVal old2 old3)

/-- `add t6, s0, s5` — payload pointer. `H+292 → H+296`. -/
theorem tshSeg2PtrAdd_spec (inPtr hdrLen v31 : Word) :
    cpsTripleWithin 1 (H + 292) (H + 296) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) ** (.x31 ↦ᵣ v31))
      ((.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) ** (.x31 ↦ᵣ (inPtr + hdrLen))) := by
  have h0 := add_spec_gen_within .x31 .x8 .x21 inPtr hdrLen v31 (H + 292) (by decide)
  rw [show (H + 292 : Word) + 4 = H + 296 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 292) 73
      (.ADD .x31 .x8 .x21)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- Store seg2 `{ptr=in+hdr, len=payloadLen}`. `H+296 → H+304`. -/
theorem tshSeg2Store_spec (payloadPtr payloadLen old4 old5 : Word) :
    cpsTripleWithin 2 (H + 296) (H + 304) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ payloadPtr) ** (.x22 ↦ᵣ payloadLen) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ payloadPtr) ** (.x22 ↦ᵣ payloadLen) **
        ((tshSegsBase + 32) ↦ₘ payloadPtr) ** ((tshSegsBase + 40) ↦ₘ payloadLen)) := by
  have h0 := sd_spec_gen_within .x30 .x31 tshSegsBase payloadPtr old4
    (32 : BitVec 12) (H + 296)
  rw [show (H + 296 : Word) + 4 = H + 300 from by decide,
      show tshSegsBase + signExtend12 (32 : BitVec 12) = tshSegsBase + 32 from by
        decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 296) 74
      (.SD .x30 .x31 (32 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0
  have c0 : cpsTripleWithin 1 (H + 296) (H + 300) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ payloadPtr) ** (.x22 ↦ᵣ payloadLen) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ payloadPtr) ** (.x22 ↦ᵣ payloadLen) **
        ((tshSegsBase + 32) ↦ₘ payloadPtr) ** ((tshSegsBase + 40) ↦ₘ old5)) := by
    have hF := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ payloadLen) ** ((tshSegsBase + 40) ↦ₘ old5)) (by pcf) l0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1 := sd_spec_gen_within .x30 .x22 tshSegsBase payloadLen old5
    (40 : BitVec 12) (H + 300)
  rw [show (H + 300 : Word) + 4 = H + 304 from by decide,
      show tshSegsBase + signExtend12 (40 : BitVec 12) = tshSegsBase + 40 from by
        decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 300) 75
      (.SD .x30 .x22 (40 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h1
  have c1 : cpsTripleWithin 1 (H + 300) (H + 304) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ payloadPtr) ** (.x22 ↦ᵣ payloadLen) **
        ((tshSegsBase + 32) ↦ₘ payloadPtr) ** ((tshSegsBase + 40) ↦ₘ old5))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ payloadPtr) ** (.x22 ↦ᵣ payloadLen) **
        ((tshSegsBase + 32) ↦ₘ payloadPtr) ** ((tshSegsBase + 40) ↦ₘ payloadLen)) := by
    have hF := cpsTripleWithin_frameR
      ((.x31 ↦ᵣ payloadPtr) ** ((tshSegsBase + 32) ↦ₘ payloadPtr)) (by pcf) l1
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- Seg2 compute + store. `H+292 → H+304`. -/
theorem tshSeg2Fill_spec (inPtr hdrLen payloadLen v31 old4 old5 : Word) :
    cpsTripleWithin (1 + 2) (H + 292) (H + 304) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) **
        (.x22 ↦ᵣ payloadLen) ** (.x31 ↦ᵣ v31) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) **
        (.x22 ↦ᵣ payloadLen) ** (.x31 ↦ᵣ (inPtr + hdrLen)) **
        ((tshSegsBase + 32) ↦ₘ (inPtr + hdrLen)) **
        ((tshSegsBase + 40) ↦ₘ payloadLen)) := by
  have hadd := tshSeg2PtrAdd_spec inPtr hdrLen v31
  have haddF := cpsTripleWithin_frameR
    ((.x30 ↦ᵣ tshSegsBase) ** (.x22 ↦ᵣ payloadLen) **
      ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5)) (by pcf) hadd
  have haddW : cpsTripleWithin 1 (H + 292) (H + 296) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) **
        (.x22 ↦ᵣ payloadLen) ** (.x31 ↦ᵣ v31) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) **
        (.x22 ↦ᵣ payloadLen) ** (.x31 ↦ᵣ (inPtr + hdrLen)) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) haddF
  have hsd := tshSeg2Store_spec (inPtr + hdrLen) payloadLen old4 old5
  have hsdF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen)) (by pcf) hsd
  have hsdW : cpsTripleWithin 2 (H + 296) (H + 304) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) **
        (.x22 ↦ᵣ payloadLen) ** (.x31 ↦ᵣ (inPtr + hdrLen)) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ hdrLen) **
        (.x22 ↦ᵣ payloadLen) ** (.x31 ↦ᵣ (inPtr + hdrLen)) **
        ((tshSegsBase + 32) ↦ₘ (inPtr + hdrLen)) **
        ((tshSegsBase + 40) ↦ₘ payloadLen)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsdF
  exact cpsTripleWithin_seq_same_cr haddW hsdW

/-- Kss ABI args: `a0:=segs, a1:=3, a2:=out`. `H+304 → H+316`. -/
theorem tshKssArgSetup_spec (outPtr v10 v11 v12 : Word) :
    cpsTripleWithin 3 (H + 304) (H + 316) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ outPtr)) := by
  have h0 := mv_spec_gen_within .x10 .x30 tshSegsBase v10 (H + 304) (by decide)
  rw [show (H + 304 : Word) + 4 = H + 308 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 304) 76 (.MV .x10 .x30)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0
  have c0 : cpsTripleWithin 1 (H + 304) (H + 308) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) := by
    have hF := cpsTripleWithin_frameR
      ((.x20 ↦ᵣ outPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) (by pcf) l0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1 := li_spec_gen_within .x11 v11 (3 : Word) (H + 308) (by decide)
  rw [show (H + 308 : Word) + 4 = H + 312 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 308) 77
      (.LI .x11 (3 : Word))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h1
  have c1 : cpsTripleWithin 1 (H + 308) (H + 312) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ v12)) := by
    have hF := cpsTripleWithin_frameR
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x12 ↦ᵣ v12)) (by pcf) l1
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have h2 := mv_spec_gen_within .x12 .x20 outPtr v12 (H + 312) (by decide)
  rw [show (H + 312 : Word) + 4 = H + 316 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 312) 78 (.MV .x12 .x20)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h2
  have c2 : cpsTripleWithin 1 (H + 312) (H + 316) fullCode
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ v12))
      ((.x30 ↦ᵣ tshSegsBase) ** (.x20 ↦ᵣ outPtr) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ outPtr)) := by
    have hF := cpsTripleWithin_frameR
      ((.x30 ↦ᵣ tshSegsBase) ** (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ (3 : Word)))
      (by pcf) l2
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-! ## Phase glue (early body)

    Compose already-proved slices toward the eventual `abiFrame` body triple. -/

/-- Setup moves + type-prefix store. `H+36 → H+68`. -/
theorem tshSetupThroughSb_spec
    (a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20 wordOld : Word)
    (halign : alignToDword TshBuf = TshBuf)
    (hvalid : isValidByteAccess TshBuf = true) :
    cpsTripleWithin (5 + 3) (H + 36) (H + 68) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
  have hm := tshSetupMoves_spec a0 a1 a2 a3 a4 v8 v9 v18 v19 v20
  have hmF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (TshBuf ↦ₘ wordOld)) (by pcf) hm
  have hmW : cpsTripleWithin 5 (H + 36) (H + 56) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (TshBuf ↦ₘ wordOld)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hmF
  have hsb := tshSetupLaSb_spec v5 a3 wordOld halign hvalid
  have hsbF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
      (.x14 ↦ᵣ a4) **
      (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x20 ↦ᵣ a4))
    (by pcf) hsb
  have hsbW : cpsTripleWithin 3 (H + 56) (H + 68) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsbF
  exact cpsTripleWithin_seq_same_cr hmW hsbW


/-! ## Phase glue: empty-length fail after setup (`H+36 → bodyExit`) -/

/-- Empty `len` (`a1 = 0`) fail path through setup + beq + `li a0,1`. -/
theorem tshSetupThenEmptyFail_spec
    (a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20 wordOld : Word)
    (halign : alignToDword TshBuf = TshBuf)
    (hvalid : isValidByteAccess TshBuf = true)
    (hlen : a1 = 0) :
    cpsTripleWithin (5 + 3 + 2) (H + 36) tshBodyExit fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
  have hsetup := tshSetupThroughSb_spec a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20
    wordOld halign hvalid
  have hsetupF := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hsetup
  have hsetupW : cpsTripleWithin (5 + 3) (H + 36) (H + 68) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsetupF
  have hfail := tshEmptyLenFail_spec a1 a0 hlen
  have hfailF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ a4) **
      (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ a4) **
      (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
    (by pcf) hfail
  have hfailW : cpsTripleWithin 2 (H + 68) tshBodyExit fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hfailF
  exact cpsTripleWithin_seq_same_cr hsetupW hfailW


/-! ## Empty-len fail body in `abiFrame_spec_own` shape -/

theorem tshFrame_cons :
    tshFrame =
      (.x1, (0 : BitVec 12)) ::
        [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
         (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
         (.x22, (56 : BitVec 12))] := rfl

abbrev tshSregs : FrameDesc :=
  [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12)),
   (.x19, (32 : BitVec 12)), (.x20, (40 : BitVec 12)), (.x21, (48 : BitVec 12)),
   (.x22, (56 : BitVec 12))]

theorem tshFrame_ne_zero : ∀ p ∈ tshFrame, p.1 ≠ .x0 := by decide

theorem tshFrame_restore (sp0 : Word) :
    (sp0 + signExtend12 (-64 : BitVec 12)) + signExtend12 (64 : BitVec 12) = sp0 :=
  sext_frameRestore sp0 (-64 : BitVec 12) (64 : BitVec 12) (by decide)

/-- Body-level empty-len caller footprint (ABI args + type-prefix dword). -/
def tshEmptyFailCallerPre (a0 a1 a2 a3 a4 v5 wordOld : Word) : Assertion :=
  (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
  (.x14 ↦ᵣ a4) ** (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (TshBuf ↦ₘ wordOld)

def tshEmptyFailCallerPost (a1 a2 a3 a4 wordOld : Word) : Assertion :=
  (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
  (.x14 ↦ᵣ a4) ** (.x5 ↦ᵣ TshBuf) ** (.x0 ↦ᵣ (0 : Word)) **
  (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))

theorem tshEmptyFailCallerPre_pcFree (a0 a1 a2 a3 a4 v5 wordOld : Word) :
    (tshEmptyFailCallerPre a0 a1 a2 a3 a4 v5 wordOld).pcFree := by
  unfold tshEmptyFailCallerPre
  repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs

theorem tshEmptyFailCallerPost_pcFree (a1 a2 a3 a4 wordOld : Word) :
    (tshEmptyFailCallerPost a1 a2 a3 a4 wordOld).pcFree := by
  unfold tshEmptyFailCallerPost
  repeat first | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_memIs

private theorem tsh_regsAt_frame (vals : Reg → Word) :
    regsAt tshFrame vals =
      ((.x1 ↦ᵣ vals .x1) ** (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
        (.x18 ↦ᵣ vals .x18) ** (.x19 ↦ᵣ vals .x19) ** (.x20 ↦ᵣ vals .x20) **
        (.x21 ↦ᵣ vals .x21) ** (.x22 ↦ᵣ vals .x22)) := by
  simp [tshFrame, regsAt_cons, regsAt_nil, sepConj_emp_right']

private theorem tsh_regsOwnAt_frame :
    regsOwnAt tshFrame =
      (regOwn .x1 ** regOwn .x8 ** regOwn .x9 ** regOwn .x18 **
        regOwn .x19 ** regOwn .x20 ** regOwn .x21 ** regOwn .x22) := by
  simp [tshFrame, regsOwnAt_cons, regsOwnAt_nil, sepConj_emp_right']

/-- Empty-len fail body under frame ownership. `bodySteps = 10`. -/
theorem tshEmptyLenFailBody
    (newSp : Word) (vals : Reg → Word)
    (a0 a1 a2 a3 a4 v5 wordOld : Word)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalid : isValidByteAccess TshBuf = true)
    (hlen : a1 = 0) :
    cpsTripleWithin (5 + 3 + 2)
      (H + BitVec.ofNat 64 (4 * (1 + tshFrame.length)))
      (H + BitVec.ofNat 64 (4 * (1 + tshFrame.length + tshBody.length)))
      fullCode
      ((.x2 ↦ᵣ newSp) ** regsAt tshFrame vals **
        frameSlotsSaved tshFrame newSp vals **
        tshEmptyFailCallerPre a0 a1 a2 a3 a4 v5 wordOld)
      ((.x2 ↦ᵣ newSp) ** regsOwnAt tshFrame **
        frameSlotsSaved tshFrame newSp vals **
        tshEmptyFailCallerPost a1 a2 a3 a4 wordOld) := by
  rw [tshFrame_length, tshBody_length]
  simp only [show 4 * (1 + 8) = 36 from rfl,
    show 4 * (1 + 8 + 74) = 332 from rfl]
  have core := tshSetupThenEmptyFail_spec a0 a1 a2 a3 a4 v5
    (vals .x8) (vals .x9) (vals .x18) (vals .x19) (vals .x20) wordOld
    halignBuf hvalid hlen
  have framed := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ vals .x1) **
      (.x21 ↦ᵣ vals .x21) ** (.x22 ↦ᵣ vals .x22) **
      frameSlotsSaved tshFrame newSp vals)
    (by pcf) core
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h hq => ?_) framed
  · rw [tsh_regsAt_frame, tshEmptyFailCallerPre] at hp
    xperm_hyp hp
  · let vals' : Reg → Word := fun
      | .x1 => vals .x1
      | .x8 => a0
      | .x9 => a1
      | .x18 => a2
      | .x19 => a3
      | .x20 => a4
      | .x21 => vals .x21
      | .x22 => vals .x22
      | r => vals r
    have hq2 : (regsAt tshFrame vals' **
        ((.x2 ↦ᵣ newSp) ** frameSlotsSaved tshFrame newSp vals **
          tshEmptyFailCallerPost a1 a2 a3 a4 wordOld)) h := by
      rw [tsh_regsAt_frame]
      unfold tshEmptyFailCallerPost at hq ⊢
      simp only [vals'] at hq ⊢
      xperm_hyp hq
    have hq3 :=
      sepConj_mono (regsAt_implies_regsOwnAt tshFrame vals') (fun _ hx => hx) h hq2
    rw [tsh_regsOwnAt_frame] at hq3 ⊢
    xperm_hyp hq3


end EvmAsm.Codegen.TxSigningHashSpec
