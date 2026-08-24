/-
  EvmAsm.Codegen.Programs.AssembleExecutionRequestsHeader

  The EIP-7685 SSZ `ExecutionRequests` offset header of
  `assemble_execution_requests` (#12206): instructions 0–13, i.e. entry
  `pc 0` → `pc 14`.

  SSZ serialises a container of five variable-length byte fields as five
  little-endian `u32` offsets followed by the bodies, each offset relative to
  the container start (`execution-specs` @ `e5a8caf1b`, the SSZ
  `ExecutionRequests` container behind
  `src/ethereum/prague/requests.py`: the wire form is
  `[off0..off4][deposits][withdrawals][consolidations][builder_deposits]
  [builder_exits]` with `off0 = 5 * 4 = 20`). The routine writes exactly that:
  `off0 = 20` and a running sum advanced by each body length.

    0   LI   x5, 20
    1   SW   x5, 0(x16)
    2   ADD  x5, x5, x11        -- + deposit len
    3   SW   x5, 4(x16)
    4   ADD  x5, x5, x13        -- + withdrawal len
    5   SW   x5, 8(x16)
    6   ADD  x5, x5, x15        -- + consolidation len
    7   SW   x5, 12(x16)
    8-9 la   x7, aer_bd_len
    10  LD   x28, 0(x7)
    11  ADD  x5, x5, x28        -- + builder-deposit len
    12  SW   x5, 16(x16)
    13  ADDI x6, x16, 20        -- the body write cursor

  The five offsets land in `out[0..20)`, which the copy loops then continue
  writing from `out+20` — one and the same `bytesRegion out …`, so the
  header/body aliasing is discharged by `setBytes` index arithmetic rather
  than assumed away.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStoreWide
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsBase

namespace EvmAsm.Codegen.AssembleExecutionRequestsHeader

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.AssembleExecutionRequestsBase

set_option maxRecDepth 8000

/-! ## The four `aer_*` globals -/

abbrev BdPtrA : Word := BitVec.ofNat 64 GuestAddrs.aer_bd_ptr
abbrev BdLenA : Word := BitVec.ofNat 64 GuestAddrs.aer_bd_len
abbrev BePtrA : Word := BitVec.ofNat 64 GuestAddrs.aer_be_ptr
abbrev BeLenA : Word := BitVec.ofNat 64 GuestAddrs.aer_be_len

/-! ## The pure header -/

/-- The five SSZ offsets, as `Word`s: `20`, then a running sum. -/
def aerOff0 : Word := 20
def aerOff1 (dl : Word) : Word := aerOff0 + dl
def aerOff2 (dl wl : Word) : Word := aerOff1 dl + wl
def aerOff3 (dl wl cl : Word) : Word := aerOff2 dl wl + cl
def aerOff4 (dl wl cl bdl : Word) : Word := aerOff3 dl wl cl + bdl

/-- The output region after the header: the five little-endian `u32` offsets
    spliced into `out[0..20)`, everything else untouched. -/
def aerHeaderBytes (ob : List (BitVec 8)) (dl wl cl bdl : Word) : List (BitVec 8) :=
  setBytes (setBytes (setBytes (setBytes
    (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
    4 (word32Bytes ((aerOff1 dl).truncate 32)))
    8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
    12 (word32Bytes ((aerOff3 dl wl cl).truncate 32)))
    16 (word32Bytes ((aerOff4 dl wl cl bdl).truncate 32))

theorem aerHeaderBytes_length (ob : List (BitVec 8)) (dl wl cl bdl : Word) :
    (aerHeaderBytes ob dl wl cl bdl).length = ob.length := by
  simp only [aerHeaderBytes, length_setBytes]

/-! ## The header state -/

/-- Header working state: the registers the header touches, the output
    region, the `aer_bd_len` global cell, and an opaque pcFree ambient `F`. -/
def HS (out dl wl cl bdl : Word) (F : Assertion)
    (v5 v6 v7 v28 : Word) (ob : List (BitVec 8)) : Assertion :=
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
  (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ out) **
  bytesRegion out ob ** (BdLenA ↦ₘ bdl) ** F

local macro "pcfH" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_emp
      | apply pcFree_sepConj)

theorem HS_pcFree (out dl wl cl bdl : Word) (F : Assertion) (hF : F.pcFree)
    (v5 v6 v7 v28 : Word) (ob : List (BitVec 8)) :
    (HS out dl wl cl bdl F v5 v6 v7 v28 ob).pcFree := by
  simp only [HS]; pcfH; exact hF

/-! ## Address bridges -/

private theorem la_bd_len_hi :
    laHi GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 32) =
      Rv64.laHi (pc 8) BdLenA := by decide

private theorem la_bd_len_lo :
    laLo GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 32) =
      Rv64.laLo (pc 8) BdLenA := by decide

private theorem la_bd_len_range : laInRange (pc 8) BdLenA := by decide

private theorem bdLenA_off0 : BdLenA + signExtend12 (0 : BitVec 12) = BdLenA := by decide

private theorem se12_20 : signExtend12 (20 : BitVec 12) = (20 : Word) := by decide

private theorem pc89 : (pc 8 : Word) + 4 = pc 9 := by decide
private theorem pc810 : (pc 8 : Word) + 8 = pc 10 := by decide

/-! ## The header triple -/

/-- **The offset header.** Fuel 14, `pc 0 → pc 14`.

    Post: `out[0..20)` holds the five little-endian `u32` SSZ offsets
    `20, 20+dl, 20+dl+wl, 20+dl+wl+cl, 20+dl+wl+cl+bdl` (each truncated to
    32 bits, as `SW` stores them), `x5` is the last running sum, `x6` is the
    body write cursor `out + 20`, `x7` points at `aer_bd_len` and `x28` holds
    its value. -/
theorem aer_header
    (out dl wl cl bdl v5 v6 v7 v28 : Word)
    (ob : List (BitVec 8))
    (hAlign : out.toNat % 8 = 0)
    (hLen : 20 ≤ ob.length)
    (hOver : out.toNat + 20 < 2 ^ 64)
    (hValid : ∀ i, i ≤ 16 → isValidMemAccess (out + BitVec.ofNat 64 i) = true)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 14 (pc 0) (pc 14) aerCode
      (HS out dl wl cl bdl F v5 v6 v7 v28 ob)
      (HS out dl wl cl bdl F (aerOff4 dl wl cl bdl) (out + 20) BdLenA bdl
        (aerHeaderBytes ob dl wl cl bdl)) := by
  -- One `SW x5, imm(x16)` step of the header, at region index `i`.
  have sw_step : ∀ (j i : Nat) (imm : BitVec 12) (val : Word) (o : List (BitVec 8))
      (w6 w7 w28 : Word),
      (∀ a k, CodeReq.singleton (pc j) (.SW .x16 .x5 imm) a = some k → aerCode a = some k) →
      signExtend12 imm = BitVec.ofNat 64 i → 4 ∣ i → i + 4 ≤ o.length → i ≤ 16 →
      cpsTripleWithin 1 (pc j) (pc (j + 1)) aerCode
        (HS out dl wl cl bdl F val w6 w7 w28 o)
        (HS out dl wl cl bdl F val w6 w7 w28
          (setBytes o i (word32Bytes (val.truncate 32)))) := by
    intro j i imm val o w6 w7 w28 hmem hse hdvd hlen hi16
    have hcore := bytesRegion_sw_at_within .x16 .x5 out out val imm (pc j) o i
      (by rw [hse]) hAlign hdvd hlen (by omega) (hValid i hi16)
    have hc := cpsTripleWithin_extend_code hmem hcore
    rw [pc_succ j] at hc
    have hfr := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28) **
       (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (BdLenA ↦ₘ bdl) ** F)
      (by pcfH; exact hF) hc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [HS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [HS] at hq ⊢; xperm_chunked hq)
      hfr
  -- One accumulating `ADD x5, x5, rs2` step, `rs2` framed out of `HS`.
  have add_step : ∀ (j : Nat) (rs2 : Reg) (val addend : Word) (o : List (BitVec 8))
      (w6 w7 w28 : Word) (Rest : Assertion), Rest.pcFree →
      (∀ a k, CodeReq.singleton (pc j) (.ADD .x5 .x5 rs2) a = some k → aerCode a = some k) →
      (∀ h, (HS out dl wl cl bdl F val w6 w7 w28 o) h →
        (((.x5 ↦ᵣ val) ** (rs2 ↦ᵣ addend)) ** Rest) h) →
      (∀ h, (((.x5 ↦ᵣ (val + addend)) ** (rs2 ↦ᵣ addend)) ** Rest) h →
        (HS out dl wl cl bdl F (val + addend) w6 w7 w28 o) h) →
      cpsTripleWithin 1 (pc j) (pc (j + 1)) aerCode
        (HS out dl wl cl bdl F val w6 w7 w28 o)
        (HS out dl wl cl bdl F (val + addend) w6 w7 w28 o) := by
    intro j rs2 val addend o w6 w7 w28 Rest hRest hmem hin hout
    have hcore := add_spec_gen_rd_eq_rs1_within .x5 rs2 val addend (pc j) (by decide)
    have hc := cpsTripleWithin_extend_code hmem hcore
    rw [pc_succ j] at hc
    exact cpsTripleWithin_weaken hin hout (cpsTripleWithin_frameR Rest hRest hc)
  -- 0: LI x5, 20
  have s0 : cpsTripleWithin 1 (pc 0) (pc 1) aerCode
      (HS out dl wl cl bdl F v5 v6 v7 v28 ob)
      (HS out dl wl cl bdl F aerOff0 v6 v7 v28 ob) := by
    have hcore := li_spec_gen_within .x5 v5 (20 : Word) (pc 0) (by decide)
    have hc := cpsTripleWithin_extend_code
      (mem_at 0 _ (pc 0) rfl (by rw [aerProgL_len]; norm_num) (by decide)) hcore
    rw [pc_succ 0] at hc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [HS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [HS, aerOff0] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
         (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ out) **
         bytesRegion out ob ** (BdLenA ↦ₘ bdl) ** F)
        (by pcfH; exact hF) hc)
  -- 1/3/5/7/12: the five `SW`s
  have s1 := sw_step 1 0 (0 : BitVec 12) aerOff0 ob v6 v7 v28
    (mem_at 1 _ (pc 1) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (by decide) ⟨0, rfl⟩ (by omega) (by omega)
  have s3 := sw_step 3 4 (4 : BitVec 12) (aerOff1 dl)
    (setBytes ob 0 (word32Bytes (aerOff0.truncate 32))) v6 v7 v28
    (mem_at 3 _ (pc 3) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (by decide) ⟨1, rfl⟩ (by rw [length_setBytes]; omega) (by omega)
  have s5 := sw_step 5 8 (8 : BitVec 12) (aerOff2 dl wl)
    (setBytes (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
      4 (word32Bytes ((aerOff1 dl).truncate 32))) v6 v7 v28
    (mem_at 5 _ (pc 5) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (by decide) ⟨2, rfl⟩ (by rw [length_setBytes, length_setBytes]; omega) (by omega)
  have s7 := sw_step 7 12 (12 : BitVec 12) (aerOff3 dl wl cl)
    (setBytes (setBytes (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
      4 (word32Bytes ((aerOff1 dl).truncate 32)))
      8 (word32Bytes ((aerOff2 dl wl).truncate 32))) v6 v7 v28
    (mem_at 7 _ (pc 7) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (by decide) ⟨3, rfl⟩
    (by rw [length_setBytes, length_setBytes, length_setBytes]; omega) (by omega)
  have s12 := sw_step 12 16 (16 : BitVec 12) (aerOff4 dl wl cl bdl)
    (setBytes (setBytes (setBytes (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
      4 (word32Bytes ((aerOff1 dl).truncate 32)))
      8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
      12 (word32Bytes ((aerOff3 dl wl cl).truncate 32))) v6 BdLenA bdl
    (mem_at 12 _ (pc 12) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (by decide) ⟨4, rfl⟩
    (by rw [length_setBytes, length_setBytes, length_setBytes, length_setBytes]; omega)
    (by omega)
  -- 2/4/6: the three register-length accumulations
  have s2 := add_step 2 .x11 aerOff0 dl
    (setBytes ob 0 (word32Bytes (aerOff0.truncate 32))) v6 v7 v28
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
     (.x16 ↦ᵣ out) ** bytesRegion out (setBytes ob 0 (word32Bytes (aerOff0.truncate 32))) **
     (BdLenA ↦ₘ bdl) ** F)
    (by pcfH; exact hF)
    (mem_at 2 _ (pc 2) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [HS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [HS]; xperm_chunked hq)
  have s4 := add_step 4 .x13 (aerOff1 dl) wl
    (setBytes (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
      4 (word32Bytes ((aerOff1 dl).truncate 32))) v6 v7 v28
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ dl) ** (.x15 ↦ᵣ cl) **
     (.x16 ↦ᵣ out) **
     bytesRegion out (setBytes (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
       4 (word32Bytes ((aerOff1 dl).truncate 32))) **
     (BdLenA ↦ₘ bdl) ** F)
    (by pcfH; exact hF)
    (mem_at 4 _ (pc 4) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [HS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [HS]; xperm_chunked hq)
  have s6 := add_step 6 .x15 (aerOff2 dl wl) cl
    (setBytes (setBytes (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
      4 (word32Bytes ((aerOff1 dl).truncate 32)))
      8 (word32Bytes ((aerOff2 dl wl).truncate 32))) v6 v7 v28
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) **
     (.x16 ↦ᵣ out) **
     bytesRegion out (setBytes (setBytes (setBytes ob 0
       (word32Bytes (aerOff0.truncate 32)))
       4 (word32Bytes ((aerOff1 dl).truncate 32)))
       8 (word32Bytes ((aerOff2 dl wl).truncate 32))) **
     (BdLenA ↦ₘ bdl) ** F)
    (by pcfH; exact hF)
    (mem_at 6 _ (pc 6) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [HS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [HS]; xperm_chunked hq)
  -- 8-9: la x7, aer_bd_len
  have s8 : cpsTripleWithin 2 (pc 8) (pc 10) aerCode
      (HS out dl wl cl bdl F (aerOff3 dl wl cl) v6 v7 v28
        (setBytes (setBytes (setBytes (setBytes ob 0
          (word32Bytes (aerOff0.truncate 32)))
          4 (word32Bytes ((aerOff1 dl).truncate 32)))
          8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
          12 (word32Bytes ((aerOff3 dl wl cl).truncate 32))))
      (HS out dl wl cl bdl F (aerOff3 dl wl cl) v6 BdLenA v28
        (setBytes (setBytes (setBytes (setBytes ob 0
          (word32Bytes (aerOff0.truncate 32)))
          4 (word32Bytes ((aerOff1 dl).truncate 32)))
          8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
          12 (word32Bytes ((aerOff3 dl wl cl).truncate 32)))) := by
    have hla := la_materialize_within (cr := aerCode) .x7 v7 (pc 8) BdLenA
      (by decide) la_bd_len_range
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 8)
            (.AUIPC .x7 (laHi GuestAddrs.aer_bd_len
              (GuestAddrs.assemble_execution_requests + 32))) a = some i := by
          rw [la_bd_len_hi]; exact hs
        exact mem_at 8 _ (pc 8) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
      (by
        intro a i hs
        have hs' : CodeReq.singleton (pc 9)
            (.ADDI .x7 .x7 (laLo GuestAddrs.aer_bd_len
              (GuestAddrs.assemble_execution_requests + 32))) a = some i := by
          rw [la_bd_len_lo, ← pc89]; exact hs
        exact mem_at 9 _ (pc 9) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    rw [pc810] at hla
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [HS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [HS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (aerOff3 dl wl cl)) ** (.x6 ↦ᵣ v6) ** (.x28 ↦ᵣ v28) **
         (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ out) **
         bytesRegion out (setBytes (setBytes (setBytes (setBytes ob 0
           (word32Bytes (aerOff0.truncate 32)))
           4 (word32Bytes ((aerOff1 dl).truncate 32)))
           8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
           12 (word32Bytes ((aerOff3 dl wl cl).truncate 32))) **
         (BdLenA ↦ₘ bdl) ** F)
        (by pcfH; exact hF) hla)
  -- 10: LD x28, 0(x7)
  have s10 : cpsTripleWithin 1 (pc 10) (pc 11) aerCode
      (HS out dl wl cl bdl F (aerOff3 dl wl cl) v6 BdLenA v28
        (setBytes (setBytes (setBytes (setBytes ob 0
          (word32Bytes (aerOff0.truncate 32)))
          4 (word32Bytes ((aerOff1 dl).truncate 32)))
          8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
          12 (word32Bytes ((aerOff3 dl wl cl).truncate 32))))
      (HS out dl wl cl bdl F (aerOff3 dl wl cl) v6 BdLenA bdl
        (setBytes (setBytes (setBytes (setBytes ob 0
          (word32Bytes (aerOff0.truncate 32)))
          4 (word32Bytes ((aerOff1 dl).truncate 32)))
          8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
          12 (word32Bytes ((aerOff3 dl wl cl).truncate 32)))) := by
    have hcore := ld_spec_gen_within .x28 .x7 BdLenA v28 bdl (0 : BitVec 12)
      (pc 10) (by decide)
    rw [bdLenA_off0] at hcore
    have hc := cpsTripleWithin_extend_code
      (mem_at 10 _ (pc 10) rfl (by rw [aerProgL_len]; norm_num) (by decide)) hcore
    rw [pc_succ 10] at hc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [HS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [HS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (aerOff3 dl wl cl)) ** (.x6 ↦ᵣ v6) **
         (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ out) **
         bytesRegion out (setBytes (setBytes (setBytes (setBytes ob 0
           (word32Bytes (aerOff0.truncate 32)))
           4 (word32Bytes ((aerOff1 dl).truncate 32)))
           8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
           12 (word32Bytes ((aerOff3 dl wl cl).truncate 32))) ** F)
        (by pcfH; exact hF) hc)
  -- 11: ADD x5, x5, x28
  have s11 := add_step 11 .x28 (aerOff3 dl wl cl) bdl
    (setBytes (setBytes (setBytes (setBytes ob 0 (word32Bytes (aerOff0.truncate 32)))
      4 (word32Bytes ((aerOff1 dl).truncate 32)))
      8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
      12 (word32Bytes ((aerOff3 dl wl cl).truncate 32))) v6 BdLenA bdl
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ BdLenA) ** (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
     (.x16 ↦ᵣ out) **
     bytesRegion out (setBytes (setBytes (setBytes (setBytes ob 0
       (word32Bytes (aerOff0.truncate 32)))
       4 (word32Bytes ((aerOff1 dl).truncate 32)))
       8 (word32Bytes ((aerOff2 dl wl).truncate 32)))
       12 (word32Bytes ((aerOff3 dl wl cl).truncate 32))) **
     (BdLenA ↦ₘ bdl) ** F)
    (by pcfH; exact hF)
    (mem_at 11 _ (pc 11) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (fun _ hp => by simp only [HS] at hp; xperm_chunked hp)
    (fun _ hq => by simp only [HS]; xperm_chunked hq)
  -- 13: ADDI x6, x16, 20
  have s13 : cpsTripleWithin 1 (pc 13) (pc 14) aerCode
      (HS out dl wl cl bdl F (aerOff4 dl wl cl bdl) v6 BdLenA bdl
        (aerHeaderBytes ob dl wl cl bdl))
      (HS out dl wl cl bdl F (aerOff4 dl wl cl bdl) (out + 20) BdLenA bdl
        (aerHeaderBytes ob dl wl cl bdl)) := by
    have hcore := addi_spec_gen_within .x6 .x16 v6 out (20 : BitVec 12) (pc 13) (by decide)
    rw [se12_20] at hcore
    have hc := cpsTripleWithin_extend_code
      (mem_at 13 _ (pc 13) rfl (by rw [aerProgL_len]; norm_num) (by decide)) hcore
    rw [pc_succ 13] at hc
    exact cpsTripleWithin_weaken
      (fun _ hp => by simp only [HS] at hp ⊢; xperm_chunked hp)
      (fun _ hq => by simp only [HS] at hq ⊢; xperm_chunked hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x7 ↦ᵣ BdLenA) ** (.x28 ↦ᵣ bdl) **
         (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) **
         bytesRegion out (aerHeaderBytes ob dl wl cl bdl) ** (BdLenA ↦ₘ bdl) ** F)
        (by pcfH; exact hF) hc)
  -- Chain.
  have c1 := cpsTripleWithin_seq_same_cr s0 s1
  have c2 := cpsTripleWithin_seq_same_cr c1 s2
  have c3 := cpsTripleWithin_seq_same_cr c2 s3
  have c4 := cpsTripleWithin_seq_same_cr c3 s4
  have c5 := cpsTripleWithin_seq_same_cr c4 s5
  have c6 := cpsTripleWithin_seq_same_cr c5 s6
  have c7 := cpsTripleWithin_seq_same_cr c6 s7
  have c8 := cpsTripleWithin_seq_same_cr c7 s8
  have c10 := cpsTripleWithin_seq_same_cr c8 s10
  have c11 := cpsTripleWithin_seq_same_cr c10 s11
  have c12 := cpsTripleWithin_seq_same_cr c11 s12
  have c13 := cpsTripleWithin_seq_same_cr c12 s13
  simpa only [aerHeaderBytes] using c13

end EvmAsm.Codegen.AssembleExecutionRequestsHeader
