/-
Copyright (c) 2025 zkSecurity. All rights reserved.
Released under Apache 2.0 license.
Authors: EvmAsm contributors

# SHA-256 final CSRS + LI a0,0 + BE squeeze setup/exit

Geometry @ B = GuestAddrs.zkvm_sha256:
- la params + CSRS @ B+396..B+408 (idx 99-101)
- squeeze setup LI0/LI32 @ B+408..B+416
- BEQ exit done=32 @ B+416 → B+448
- LI a0,0 @ B+448 → bodyExit B+452

Machine squeeze body loop: `HashBridgeSha256SqueezeLoop.lean`
(`sha256Squeeze_loop`, composed as `sha256SqueezeToExit_spec` B+396→B+452).
-/
import EvmAsm.Codegen.Proofs.HashBridgeSha256Block
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.GenericSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.MemRegion
import Mathlib.Data.Nat.Bitwise

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL
private abbrev ShaParams : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins
    sha256ProgL_bound a i h

local macro "pcf" : tactic =>
  `(tactic| repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _
    | assumption)

private theorem la_final_params_hi :
    Codegen.laHi GuestAddrs.sha256_w_params (GuestAddrs.zkvm_sha256 + 396) =
      Rv64.laHi (B + 396) ShaParams := by decide

private theorem la_final_params_lo :
    Codegen.laLo GuestAddrs.sha256_w_params (GuestAddrs.zkvm_sha256 + 396) =
      Rv64.laLo (B + 396) ShaParams := by decide

private theorem la_final_params_range : laInRange (B + 396) ShaParams := by decide

theorem sha256FinalLaParams_spec (v10 : Word) :
    cpsTripleWithin 2 (B + 396) (B + 404) sha256Cr
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ ShaParams) := by
  have hau : ∀ a i,
      CodeReq.singleton (B + 396)
        (.AUIPC .x10 (Rv64.laHi (B + 396) ShaParams)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 99
      (.AUIPC .x10 (Codegen.laHi GuestAddrs.sha256_w_params
        (GuestAddrs.zkvm_sha256 + 396))) (B + 396) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← la_final_params_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((B + 396) + 4)
        (.ADDI .x10 .x10 (Rv64.laLo (B + 396) ShaParams)) a = some i →
        sha256Cr a = some i := by
    intro a i hi
    have hmem := mem_at 100
      (.ADDI .x10 .x10 (Codegen.laLo GuestAddrs.sha256_w_params
        (GuestAddrs.zkvm_sha256 + 396))) (B + 400) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)
    have hpc : (B + 396 : Word) + 4 = B + 400 := by decide
    rw [hpc, ← la_final_params_lo] at hi
    exact hmem a i hi
  exact la_materialize_within .x10 v10 (B + 396) ShaParams
    (by decide) la_final_params_range hau had

/-- Final CSRS after bitlen: la + CSRS. Fuel 3. B+396 → B+408. -/
theorem sha256FinalCsrs_spec
    (scratchBase stateBase paramsBase : Word)
    (scratch state params : List (BitVec 8)) (payload : List Word)
    (v10 : Word)
    (hstate : state.length = 32) (hpayload : payload.length = 4)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase state ** bytesRegion scratchBase scratch) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 3 (B + 396) (B + 408) sha256Cr
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch)
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params **
        bytesRegion stateBase (setBytes state 0 (payload.flatMap dwordBytes)) **
        bytesRegion scratchBase scratch) := by
  have hla := sha256FinalLaParams_spec v10
  have hlaF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ stateBase) ** (.x21 ↦ᵣ scratchBase) **
      bytesRegion paramsBase params ** bytesRegion stateBase state **
      bytesRegion scratchBase scratch) (by pcf) hla
  have hla' : cpsTripleWithin 2 (B + 396) (B + 404) sha256Cr
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch)
      ((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) ** (.x21 ↦ᵣ scratchBase) **
        bytesRegion paramsBase params ** bytesRegion stateBase state **
        bytesRegion scratchBase scratch) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hlaF
  have hcs := sha256ExternalCsrs_regs_spec_within (B + 404)
    paramsBase stateBase scratchBase params state scratch payload
    stateBase ShaParams scratchBase hstate hpayload hsem
  have hcs' := cpsTripleWithin_extend_code
    (mem_at 101 (.CSRS 0x805 .x10) (B + 404) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hcs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp)
    hla' hcs'

/-- XORI rd, rs1, imm with distinct rd (squeeze xori t2,i,3). -/
theorem xori_spec_gen_within (rd rs1 : Reg) (vOld v1 : Word)
    (imm : BitVec 12) (addr : Word) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.XORI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ vOld))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 ^^^ signExtend12 imm))) :=
  generic_2reg_spec_within (.XORI rd rs1 imm) rs1 rd v1 vOld
    (v1 ^^^ signExtend12 imm) addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem hfetch (by nofun) (by nofun) (by rfl))

private theorem se12_3 : signExtend12 (3 : BitVec 12) = (3 : Word) := by decide

/-- LI a0,0 @ B+448 → B+452 (bodyExit). -/
theorem sha256Li0_spec (v10 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 448) (B + 452) sha256Cr
      ((.x10 ↦ᵣ v10) ** F)
      ((.x10 ↦ᵣ (0 : Word)) ** F) := by
  have h0 := li_spec_gen_within .x10 v10 (0 : Word) (B + 448) (by decide)
  have h := cpsTripleWithin_extend_code
    (mem_at 112 (.LI .x10 (0 : Word)) (B + 448) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h0
  have hpc : (B + 448 : Word) + 4 = B + 452 := by decide
  rw [hpc] at h
  exact cpsTripleWithin_frameR F hF h

/-- LI x5,0; LI x6,32 @ B+408 → B+416 (squeeze loop entry). -/
theorem sha256SqueezeSetup_spec (v5 v6 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 2 (B + 408) (B + 416) sha256Cr
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** F)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** F) := by
  have h5 := li_spec_gen_within .x5 v5 (0 : Word) (B + 408) (by decide)
  have c5 := cpsTripleWithin_extend_code
    (mem_at 102 (.LI .x5 (0 : Word)) (B + 408) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h5
  have hpc5 : (B + 408 : Word) + 4 = B + 412 := by decide
  rw [hpc5] at c5
  have c5F := cpsTripleWithin_frameR ((.x6 ↦ᵣ v6) ** F)
    (by first | exact hF | pcf) c5
  have c5' : cpsTripleWithin 1 (B + 408) (B + 412) sha256Cr
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** F)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) c5F
  have h6 := li_spec_gen_within .x6 v6 (32 : Word) (B + 412) (by decide)
  have c6 := cpsTripleWithin_extend_code
    (mem_at 103 (.LI .x6 (32 : Word)) (B + 412) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h6
  have hpc6 : (B + 412 : Word) + 4 = B + 416 := by decide
  rw [hpc6] at c6
  have c6F := cpsTripleWithin_frameR ((.x5 ↦ᵣ (0 : Word)) ** F)
    (by first | exact hF | pcf) c6
  have c6' : cpsTripleWithin 1 (B + 412) (B + 416) sha256Cr
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** F)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (32 : Word)) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) c6F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) c5' c6'

/-- Pure BE squeeze of a 32-byte LE state buffer (i ↦ state[i ^^^ 3]). -/
def sha256SqueezeBE (st : List (BitVec 8)) : List (BitVec 8) :=
  (List.range 32).map (fun i => st.getD (i ^^^ 3) 0)

theorem sha256SqueezeBE_length (st : List (BitVec 8)) :
    (sha256SqueezeBE st).length = 32 := by
  simp [sha256SqueezeBE]

theorem xor3_lt_32 (done : Nat) (hd : done < 32) : done ^^^ 3 < 32 := by
  have h := Nat.xor_lt_two_pow (x := done) (y := 3) (n := 5)
    (by omega) (by decide)
  omega

theorem ofNat_xor3 (done : Nat) (hd : done < 32) :
    BitVec.ofNat 64 done ^^^ (3 : Word) = BitVec.ofNat 64 (done ^^^ 3) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : done < 2 ^ 64 := Nat.lt_trans hd (by decide)
  have h2 := xor3_lt_32 done hd
  have h3 : done ^^^ 3 < 2 ^ 64 := Nat.lt_trans h2 (by decide)
  have h3w : (3 : Word).toNat = 3 := by decide
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, h3w]
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3]

/-- Inv at BEQ hdr B+416. -/
def sha256SqueezeInv (stateBase outBase : Word) (st out : List (BitVec 8))
    (done : Nat) (F : Assertion) : Assertion :=
  (.x5 ↦ᵣ BitVec.ofNat 64 done) ** (.x6 ↦ᵣ (32 : Word)) **
    (.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
    bytesRegion stateBase st ** bytesRegion outBase out **
    regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F

/-- BEQ taken done=32 → B+448. -/
theorem sha256Squeeze_exit
    (stateBase outBase : Word) (st out : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 1 (B + 416) (B + 448) sha256Cr
      (sha256SqueezeInv stateBase outBase st out 32 F)
      (sha256SqueezeInv stateBase outBase st out 32 F) := by
  unfold sha256SqueezeInv
  have hbr := beq_spec_gen_within .x5 .x6 (32 : BitVec 13)
    (BitVec.ofNat 64 32) (32 : Word) (B + 416)
  have hbrC := cpsBranchWithin_extend_code
    (mem_at 104 (.BEQ .x5 .x6 (32 : BitVec 13)) (B + 416) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hbr
  have hbrT := cpsBranchWithin_takenStripPure2 hbrC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  rw [show (B + 416 : Word) + signExtend13 (32 : BitVec 13) = B + 448 from by decide]
    at hbrT
  have hbrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ stateBase) ** (.x19 ↦ᵣ outBase) **
      bytesRegion stateBase st ** bytesRegion outBase out **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** F)
    (by first | exact hF | pcf) hbrT
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hbrF

end EvmAsm.Codegen.Proofs
