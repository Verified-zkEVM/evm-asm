/-
  EvmAsm.Codegen.Programs.AssembleExecutionRequestsTop

  The whole-routine triple for `assemble_execution_requests` (#12206):
  entry `GuestAddrs.assemble_execution_requests` through the `JALR` return.

  Composition of seven segments, all over the routine's own `CodeReq`
  (`aerCode`) — the routine calls nothing, so there is no callee residual:

    pc 0  → pc 14   `aer_header`   offset header + write cursor
    pc 14 → pc 23   `aer_mv_loop`  deposits        (a0/a1)
    pc 23 → pc 32   `aer_mv_loop`  withdrawals     (a2/a3)
    pc 32 → pc 41   `aer_mv_loop`  consolidations  (a4/a5)
    pc 41 → pc 54   `aer_la_loop`  builder deposits (`aer_bd_*`)
    pc 54 → pc 67   `aer_la_loop`  builder exits    (`aer_be_*`)
    pc 67 → ret     `aer_tail`     a0 = total section length

  Domain restriction (recorded in the registry row): the precondition holds
  the output region and the five body regions as SEPARATE `bytesRegion`
  conjuncts, so the output buffer must not overlap any source body. That is a
  real requirement of the routine — the copy loops read and write byte by
  byte with no overlap handling — not a proof convenience.
-/

import EvmAsm.Codegen.Programs.AssembleExecutionRequestsBody
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsHeader
import EvmAsm.Codegen.Programs.AssembleExecutionRequestsTail

namespace EvmAsm.Codegen.AssembleExecutionRequestsTop

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.AssembleExecutionRequestsBase
open EvmAsm.Codegen.AssembleExecutionRequestsCopy
open EvmAsm.Codegen.AssembleExecutionRequestsBody
open EvmAsm.Codegen.AssembleExecutionRequestsHeader
open EvmAsm.Codegen.AssembleExecutionRequestsTail

set_option maxRecDepth 8000

local macro "pcfA" : tactic =>
  `(tactic| repeat' first
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_emp
      | apply pcFree_sepConj)

/-! ## The five loop sites -/

private theorem cc16 : CopyCode 16 :=
  ⟨mem_at 16 _ (pc 16) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 17 _ (pc 17) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 18 _ (pc 18) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 19 _ (pc 19) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 20 _ (pc 20) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 21 _ (pc 21) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 22 _ (pc 22) rfl (by rw [aerProgL_len]; norm_num) (by decide)⟩

private theorem cc25 : CopyCode 25 :=
  ⟨mem_at 25 _ (pc 25) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 26 _ (pc 26) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 27 _ (pc 27) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 28 _ (pc 28) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 29 _ (pc 29) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 30 _ (pc 30) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 31 _ (pc 31) rfl (by rw [aerProgL_len]; norm_num) (by decide)⟩

private theorem cc34 : CopyCode 34 :=
  ⟨mem_at 34 _ (pc 34) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 35 _ (pc 35) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 36 _ (pc 36) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 37 _ (pc 37) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 38 _ (pc 38) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 39 _ (pc 39) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 40 _ (pc 40) rfl (by rw [aerProgL_len]; norm_num) (by decide)⟩

private theorem cc47 : CopyCode 47 :=
  ⟨mem_at 47 _ (pc 47) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 48 _ (pc 48) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 49 _ (pc 49) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 50 _ (pc 50) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 51 _ (pc 51) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 52 _ (pc 52) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 53 _ (pc 53) rfl (by rw [aerProgL_len]; norm_num) (by decide)⟩

private theorem cc60 : CopyCode 60 :=
  ⟨mem_at 60 _ (pc 60) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 61 _ (pc 61) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 62 _ (pc 62) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 63 _ (pc 63) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 64 _ (pc 64) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 65 _ (pc 65) rfl (by rw [aerProgL_len]; norm_num) (by decide),
   mem_at 66 _ (pc 66) rfl (by rw [aerProgL_len]; norm_num) (by decide)⟩

/-! ## `la` bridges for the two globals-driven segments -/

private theorem la_bdp_hi :
    laHi GuestAddrs.aer_bd_ptr (GuestAddrs.assemble_execution_requests + 164) =
      Rv64.laHi (pc 41) BdPtrA := by decide
private theorem la_bdp_lo :
    laLo GuestAddrs.aer_bd_ptr (GuestAddrs.assemble_execution_requests + 164) =
      Rv64.laLo (pc 41) BdPtrA := by decide
private theorem la_bdl_hi :
    laHi GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 176) =
      Rv64.laHi (pc 44) BdLenA := by decide
private theorem la_bdl_lo :
    laLo GuestAddrs.aer_bd_len (GuestAddrs.assemble_execution_requests + 176) =
      Rv64.laLo (pc 44) BdLenA := by decide
private theorem la_bep_hi :
    laHi GuestAddrs.aer_be_ptr (GuestAddrs.assemble_execution_requests + 216) =
      Rv64.laHi (pc 54) BePtrA := by decide
private theorem la_bep_lo :
    laLo GuestAddrs.aer_be_ptr (GuestAddrs.assemble_execution_requests + 216) =
      Rv64.laLo (pc 54) BePtrA := by decide
private theorem la_bel_hi :
    laHi GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 228) =
      Rv64.laHi (pc 57) BeLenA := by decide
private theorem la_bel_lo :
    laLo GuestAddrs.aer_be_len (GuestAddrs.assemble_execution_requests + 228) =
      Rv64.laLo (pc 57) BeLenA := by decide

private theorem pc4142 : (pc 41 : Word) + 4 = pc 42 := by decide
private theorem pc4445 : (pc 44 : Word) + 4 = pc 45 := by decide
private theorem pc5455 : (pc 54 : Word) + 4 = pc 55 := by decide
private theorem pc5758 : (pc 57 : Word) + 4 = pc 58 := by decide

private theorem w20 : (20 : Word) = BitVec.ofNat 64 20 := rfl

/-! ## The assembled section -/

/-- The output region after the whole routine: the five-offset header, then
    the five bodies concatenated at `out+20`. -/
def aerSection (ob : List (BitVec 8)) (dl wl cl bdl : Word)
    (dep wdb cns bdb beb : List (BitVec 8)) : List (BitVec 8) :=
  setBytes (setBytes (setBytes (setBytes
    (setBytes (aerHeaderBytes ob dl wl cl bdl) 20 dep)
    (20 + dep.length) wdb)
    (20 + dep.length + wdb.length) cns)
    (20 + dep.length + wdb.length + cns.length) bdb)
    (20 + dep.length + wdb.length + cns.length + bdb.length) beb

/-- Fuel: 50 straight-line steps plus 7 per copied body byte. -/
def aerFuel (bodyBytes : Nat) : Nat := 50 + 7 * bodyBytes

/-! ## The whole-routine triple -/

/-- **`assemble_execution_requests`, whole routine.**

    Pre: the ABI registers (`a0`–`a6`), the four `aer_*` globals, the output
    region and the five body regions, all separately owned.

    Post:
    * `out[0..20)` holds the five little-endian `u32` SSZ offsets
      `20, 20+dl, 20+dl+wl, 20+dl+wl+cl, 20+dl+wl+cl+bdl`;
    * `out[20..)` holds `deposits ‖ withdrawals ‖ consolidations ‖
      builder_deposits ‖ builder_exits`, in that order;
    * `a0 = 20 + dl + wl + cl + bdl + bel`, the total section length.

    The five body regions are unchanged, and the exit PC is `ra &&& ~~~1`. -/
theorem assemble_execution_requests_spec_within
    (out ra dp dl wp wl cp cl bdp bdl bep bel : Word)
    (v5 v6 v7 v28 : Word)
    (dep wdb cns bdb beb ob : List (BitVec 8))
    (ntot : Nat)
    (hntot : ntot = 20 + dep.length + wdb.length + cns.length + bdb.length + beb.length)
    (hdl : dl = BitVec.ofNat 64 dep.length)
    (hwl : wl = BitVec.ofNat 64 wdb.length)
    (hcl : cl = BitVec.ofNat 64 cns.length)
    (hbdl : bdl = BitVec.ofNat 64 bdb.length)
    (hbel : bel = BitVec.ofNat 64 beb.length)
    (hAlignOut : out.toNat % 8 = 0)
    (hAlignDep : dp.toNat % 8 = 0) (hAlignWd : wp.toNat % 8 = 0)
    (hAlignCns : cp.toNat % 8 = 0) (hAlignBd : bdp.toNat % 8 = 0)
    (hAlignBe : bep.toNat % 8 = 0)
    (hFit : ntot ≤ ob.length)
    (hOutOver : out.toNat + ntot < 2 ^ 64)
    (hDepOver : dp.toNat + dep.length < 2 ^ 64)
    (hWdOver : wp.toNat + wdb.length < 2 ^ 64)
    (hCnsOver : cp.toNat + cns.length < 2 ^ 64)
    (hBdOver : bdp.toNat + bdb.length < 2 ^ 64)
    (hBeOver : bep.toNat + beb.length < 2 ^ 64)
    (hvOutW : ∀ i, i ≤ 16 → isValidMemAccess (out + BitVec.ofNat 64 i) = true)
    (hvOutB : ∀ i, i < ntot → isValidByteAccess (out + BitVec.ofNat 64 i) = true)
    (hvDep : ∀ i, i < dep.length → isValidByteAccess (dp + BitVec.ofNat 64 i) = true)
    (hvWd : ∀ i, i < wdb.length → isValidByteAccess (wp + BitVec.ofNat 64 i) = true)
    (hvCns : ∀ i, i < cns.length → isValidByteAccess (cp + BitVec.ofNat 64 i) = true)
    (hvBd : ∀ i, i < bdb.length → isValidByteAccess (bdp + BitVec.ofNat 64 i) = true)
    (hvBe : ∀ i, i < beb.length → isValidByteAccess (bep + BitVec.ofNat 64 i) = true)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin (aerFuel (ntot - 20)) (pc 0) (ra &&& ~~~1) aerCode
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ out) **
       bytesRegion out ob ** (BdLenA ↦ₘ bdl) **
       ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x29 **
        bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
        bytesRegion bdp bdb ** bytesRegion bep beb **
        (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ dp) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
        (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** (BeLenA ↦ₘ bel) ** A))
      ((.x10 ↦ᵣ (aerTotal dl wl cl bdl bel)) **
       (.x7 ↦ᵣ BeLenA) ** (.x28 ↦ᵣ bel) **
       (.x11 ↦ᵣ dl) ** (.x13 ↦ᵣ wl) ** (.x15 ↦ᵣ cl) ** (.x1 ↦ᵣ ra) **
       (BdLenA ↦ₘ bdl) ** (BeLenA ↦ₘ bel) **
       ((.x6 ↦ᵣ (out + BitVec.ofNat 64 ntot)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x29 **
        bytesRegion out (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
        bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
        bytesRegion bdp bdb ** bytesRegion bep beb **
        (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
        (.x16 ↦ᵣ out) ** (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** A)) := by
  subst hntot
  -- Header, pc 0 → pc 14.
  have hHdr := aer_header out dl wl cl bdl v5 v6 v7 v28 ob hAlignOut
    (by omega) (by omega) hvOutW
    ((.x0 ↦ᵣ (0 : Word)) ** regOwn .x29 **
     bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
     bytesRegion bdp bdb ** bytesRegion bep beb **
     (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ dp) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
     (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** (BeLenA ↦ₘ bel) ** A)
    (by pcfA; exact hA)
  -- Deposits, pc 14 → pc 23.
  have hS1 := aer_mv_loop 14 cc16 .x10 .x11
    (mem_at 14 _ (pc 14) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (mem_at 15 _ (pc 15) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    dp out dl BdLenA bdl dep
    (aerHeaderBytes ob dl wl cl bdl) 20 hdl hAlignDep hAlignOut
    (by rw [aerHeaderBytes_length]; omega) hDepOver (by omega)
    hvDep (fun i hi => hvOutB (20 + i) (by omega))
    (bytesRegion wp wdb ** bytesRegion cp cns ** bytesRegion bdp bdb **
     bytesRegion bep beb ** (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x1 ↦ᵣ ra) **
     (.x12 ↦ᵣ wp) ** (.x13 ↦ᵣ wl) ** (.x14 ↦ᵣ cp) ** (.x15 ↦ᵣ cl) **
     (.x16 ↦ᵣ out) ** (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
     (BeLenA ↦ₘ bel) ** A)
    (by pcfA; exact hA)
  -- Withdrawals, pc 23 → pc 32.
  have hS2 := aer_mv_loop 23 cc25 .x12 .x13
    (mem_at 23 _ (pc 23) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (mem_at 24 _ (pc 24) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    wp out wl (dp + BitVec.ofNat 64 dep.length) (0 : Word) wdb
    (setBytes (aerHeaderBytes ob dl wl cl bdl) 20 dep) (20 + dep.length)
    hwl hAlignWd hAlignOut
    (by simp only [length_setBytes, aerHeaderBytes_length]; omega) hWdOver (by omega)
    hvWd (fun i hi => hvOutB (20 + dep.length + i) (by omega))
    (bytesRegion dp dep ** bytesRegion cp cns ** bytesRegion bdp bdb **
     bytesRegion bep beb ** (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x1 ↦ᵣ ra) **
     (.x10 ↦ᵣ dp) ** (.x11 ↦ᵣ dl) ** (.x14 ↦ᵣ cp) ** (.x15 ↦ᵣ cl) **
     (.x16 ↦ᵣ out) ** (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
     (BeLenA ↦ₘ bel) ** A)
    (by pcfA; exact hA)
  -- Consolidations, pc 32 → pc 41.
  have hS3 := aer_mv_loop 32 cc34 .x14 .x15
    (mem_at 32 _ (pc 32) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (mem_at 33 _ (pc 33) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    cp out cl (wp + BitVec.ofNat 64 wdb.length) (0 : Word) cns
    (setBytes (setBytes (aerHeaderBytes ob dl wl cl bdl) 20 dep)
      (20 + dep.length) wdb) (20 + dep.length + wdb.length)
    hcl hAlignCns hAlignOut
    (by simp only [length_setBytes, aerHeaderBytes_length]; omega) hCnsOver (by omega)
    hvCns (fun i hi => hvOutB (20 + dep.length + wdb.length + i) (by omega))
    (bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion bdp bdb **
     bytesRegion bep beb ** (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x1 ↦ᵣ ra) **
     (.x10 ↦ᵣ dp) ** (.x11 ↦ᵣ dl) ** (.x12 ↦ᵣ wp) ** (.x13 ↦ᵣ wl) **
     (.x16 ↦ᵣ out) ** (BdPtrA ↦ₘ bdp) ** (BdLenA ↦ₘ bdl) ** (BePtrA ↦ₘ bep) **
     (BeLenA ↦ₘ bel) ** A)
    (by pcfA; exact hA)
  -- Builder deposits, pc 41 → pc 54.
  have hS4 := aer_la_loop 41 cc47 BdPtrA BdLenA (by decide) (by decide)
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 41)
          (.AUIPC .x7 (laHi GuestAddrs.aer_bd_ptr
            (GuestAddrs.assemble_execution_requests + 164))) a = some i := by
        rw [la_bdp_hi]; exact hs
      exact mem_at 41 _ (pc 41) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 42)
          (.ADDI .x7 .x7 (laLo GuestAddrs.aer_bd_ptr
            (GuestAddrs.assemble_execution_requests + 164))) a = some i := by
        rw [la_bdp_lo, ← pc4142]; exact hs
      exact mem_at 42 _ (pc 42) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (mem_at 43 _ (pc 43) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 44)
          (.AUIPC .x28 (laHi GuestAddrs.aer_bd_len
            (GuestAddrs.assemble_execution_requests + 176))) a = some i := by
        rw [la_bdl_hi]; exact hs
      exact mem_at 44 _ (pc 44) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 45)
          (.ADDI .x28 .x28 (laLo GuestAddrs.aer_bd_len
            (GuestAddrs.assemble_execution_requests + 176))) a = some i := by
        rw [la_bdl_lo, ← pc4445]; exact hs
      exact mem_at 45 _ (pc 45) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (mem_at 46 _ (pc 46) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    bdp out bdl (cp + BitVec.ofNat 64 cns.length) (0 : Word) bdb
    (setBytes (setBytes (setBytes (aerHeaderBytes ob dl wl cl bdl) 20 dep)
      (20 + dep.length) wdb) (20 + dep.length + wdb.length) cns)
    (20 + dep.length + wdb.length + cns.length)
    hbdl hAlignBd hAlignOut
    (by simp only [length_setBytes, aerHeaderBytes_length]; omega) hBdOver (by omega)
    hvBd (fun i hi => hvOutB (20 + dep.length + wdb.length + cns.length + i) (by omega))
    (bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
     bytesRegion bep beb ** (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x1 ↦ᵣ ra) **
     (.x10 ↦ᵣ dp) ** (.x11 ↦ᵣ dl) ** (.x12 ↦ᵣ wp) ** (.x13 ↦ᵣ wl) **
     (.x14 ↦ᵣ cp) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ out) ** (BePtrA ↦ₘ bep) **
     (BeLenA ↦ₘ bel) ** A)
    (by pcfA; exact hA)
  -- Builder exits, pc 54 → pc 67.
  have hS5 := aer_la_loop 54 cc60 BePtrA BeLenA (by decide) (by decide)
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 54)
          (.AUIPC .x7 (laHi GuestAddrs.aer_be_ptr
            (GuestAddrs.assemble_execution_requests + 216))) a = some i := by
        rw [la_bep_hi]; exact hs
      exact mem_at 54 _ (pc 54) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 55)
          (.ADDI .x7 .x7 (laLo GuestAddrs.aer_be_ptr
            (GuestAddrs.assemble_execution_requests + 216))) a = some i := by
        rw [la_bep_lo, ← pc5455]; exact hs
      exact mem_at 55 _ (pc 55) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (mem_at 56 _ (pc 56) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 57)
          (.AUIPC .x28 (laHi GuestAddrs.aer_be_len
            (GuestAddrs.assemble_execution_requests + 228))) a = some i := by
        rw [la_bel_hi]; exact hs
      exact mem_at 57 _ (pc 57) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (by
      intro a i hs
      have hs' : CodeReq.singleton (pc 58)
          (.ADDI .x28 .x28 (laLo GuestAddrs.aer_be_len
            (GuestAddrs.assemble_execution_requests + 228))) a = some i := by
        rw [la_bel_lo, ← pc5758]; exact hs
      exact mem_at 58 _ (pc 58) rfl (by rw [aerProgL_len]; norm_num) (by decide) a i hs')
    (mem_at 59 _ (pc 59) rfl (by rw [aerProgL_len]; norm_num) (by decide))
    bep out bel (bdp + BitVec.ofNat 64 bdb.length) (0 : Word) beb
    (setBytes (setBytes (setBytes (setBytes (aerHeaderBytes ob dl wl cl bdl) 20 dep)
      (20 + dep.length) wdb) (20 + dep.length + wdb.length) cns)
      (20 + dep.length + wdb.length + cns.length) bdb)
    (20 + dep.length + wdb.length + cns.length + bdb.length)
    hbel hAlignBe hAlignOut
    (by simp only [length_setBytes, aerHeaderBytes_length]; omega) hBeOver (by omega)
    hvBe (fun i hi =>
      hvOutB (20 + dep.length + wdb.length + cns.length + bdb.length + i) (by omega))
    (bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
     bytesRegion bdp bdb ** (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x1 ↦ᵣ ra) **
     (.x10 ↦ᵣ dp) ** (.x11 ↦ᵣ dl) ** (.x12 ↦ᵣ wp) ** (.x13 ↦ᵣ wl) **
     (.x14 ↦ᵣ cp) ** (.x15 ↦ᵣ cl) ** (.x16 ↦ᵣ out) ** (BdPtrA ↦ₘ bdp) **
     (BdLenA ↦ₘ bdl) ** A)
    (by pcfA; exact hA)
  -- Return value, pc 67 → ret.
  have hTail := aer_tail dl wl cl bdl bel ra dp
    (bep + BitVec.ofNat 64 beb.length) (0 : Word)
    ((.x6 ↦ᵣ (out + BitVec.ofNat 64
        (20 + dep.length + wdb.length + cns.length + bdb.length + beb.length))) **
     (.x0 ↦ᵣ (0 : Word)) ** regOwn .x29 **
     bytesRegion out (aerSection ob dl wl cl bdl dep wdb cns bdb beb) **
     bytesRegion dp dep ** bytesRegion wp wdb ** bytesRegion cp cns **
     bytesRegion bdp bdb ** bytesRegion bep beb **
     (.x5 ↦ᵣ (aerOff4 dl wl cl bdl)) ** (.x12 ↦ᵣ wp) ** (.x14 ↦ᵣ cp) **
     (.x16 ↦ᵣ out) ** (BdPtrA ↦ₘ bdp) ** (BePtrA ↦ₘ bep) ** A)
    (by simp only [aerSection]; pcfA; exact hA)
  -- Chain the seven segments.
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ h => by simp only [HS, SA, w20] at h ⊢; xperm_chunked h) hHdr hS1
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ h => by simp only [SA] at h ⊢; xperm_chunked h) c1 hS2
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ h => by simp only [SA] at h ⊢; xperm_chunked h) c2 hS3
  have c4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ h => by simp only [SA, SLa] at h ⊢; xperm_chunked h) c3 hS4
  have c5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ h => by simp only [SLa] at h ⊢; xperm_chunked h) c4 hS5
  have c6 := cpsTripleWithin_seq_perm_same_cr
    (fun _ h => by simp only [SLa, TS, aerSection] at h ⊢; xperm_chunked h) c5 hTail
  exact cpsTripleWithin_mono_nSteps (by simp only [aerFuel, copyFuel]; omega) c6

end EvmAsm.Codegen.AssembleExecutionRequestsTop
