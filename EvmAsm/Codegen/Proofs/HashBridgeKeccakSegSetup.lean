/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegSetup

  Shared scaffolding for the `zkvm_keccak256_segments` machine proof
  (GH #12108 / the `tx_signing_hash` lane): the concrete guest entry, the
  `CodeReq` over the REAL emitted program, the ABI-frame decomposition, and
  the body-entry setup run (three ABI moves, `la x19, zk3_state`, the 25-dword
  sponge zeroing loop, and the `li s4, 0` rate-fill initialisation).

  ## Why a separate entry point exists at all

  `zkvm_keccak256` hashes ONE buffer.  `zkvm_keccak256_segments` hashes the
  concatenation of an N-element `(ptr, len)` descriptor array **without
  materialising it**, carrying the 0..135 rate-block fill offset in `s4` across
  segment boundaries.  That is why `tx_signing_hash` (and hence the EIP-7702
  authorization digest) reaches keccak through THIS routine and not through
  `zkvm_keccak256`, and why the landed `zkvm_keccak256_spec_within` does not
  cover it.

  ## The frame is derived, not assumed

  `kssProg_eq_abiFrame` (`decide`) pins the emitted 70-instruction program to
  `abiFrameProg (-64) 64 kssFrame kssBody` — a `ra` + seven callee-saved slot
  frame.  So the prologue/epilogue, the callee-saved round trip and the `sp`
  restore all come from `abiFrame_spec_own`; nothing about them is hypothesised
  here.

  ## Instruction map (absolute program indices)

  | idx | PC       | instruction                    | role                |
  |----:|----------|--------------------------------|---------------------|
  | 0-8 | B+0..32  | `addi sp,-64` + 8 × `sd`       | prologue (frame)    |
  | 9-11| B+36..44 | `mv s0,a0; mv s1,a1; mv s2,a2` | ABI moves           |
  |12-13| B+48,52  | `la s3, zk3_state`             | sponge arena        |
  |14-15| B+56,60  | `mv t0,s3; li t1,25`           | zero-loop prep      |
  |16-19| B+64..76 | 25-dword zero loop             | sponge := 0         |
  |  20 | B+80     | `li s4, 0`                     | rate fill := 0      |
  |  21 | B+84     | `beq s1,zero,+80`              | OUTER loop head     |
  |22-25| B+88..100| load `(ptr,len)`, bump, `s1--` | segment fetch       |
  |  26 | B+104    | `beq s6,zero,-20`              | INNER loop head     |
  |27-36| B+108..144| byte XOR into `s3[s4]`, `s4++`| absorb one byte     |
  |37-40| B+148..160| `csrs 0x800`; `s4 := 0`       | rate-block permute  |
  |41-48| B+164..192| pad `0x01` at `s4`, `0x80` @135| pad10*1            |
  |49-50| B+196,200| `mv a0,s3; csrs 0x800`         | final permute       |
  |51-58| B+204..232| 4 × (`ld`/`sd`)               | squeeze 32 bytes    |
  |  59 | B+236    | `li a0, 0`                     | status = success    |
  |60-69| B+240..276| epilogue + `ret`              | frame (derived)     |

  Body entry is `B+36`, body exit `B+240`.

  No elaboration budget is widened in this module beyond `maxRecDepth`.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakZero
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## The routine, its code requirement, and the frame decomposition -/

/-- Guest entry PC of `zkvm_keccak256_segments` (concrete, from `GuestAddrs`). -/
abbrev KssB : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256_segments

/-- The shared 200-byte sponge arena (`zk3_state`). -/
abbrev KssZk3 : Word := BitVec.ofNat 64 GuestAddrs.zk3_state

/-- `Program` → `List Instr` so `GetElem` reduces. -/
abbrev kssProgL : List Instr := zkvmKeccak256Segments_prog

theorem kssProgL_len : kssProgL.length = 70 := by
  simp only [kssProgL, zkvmKeccak256Segments_prog, zkvmKeccak256Segments_prog_of]
  decide

theorem kssProgL_bound : 4 * kssProgL.length < 2 ^ 64 := by
  rw [kssProgL_len]; norm_num

/-- **The code requirement is the real emitted program at the real address.**
    Every triple below quantifies over states satisfying exactly this, so no
    executed address is left unconstrained (the `wlCallWithinShape` failure
    mode). The routine is a LEAF: its only non-local instruction is the
    `csrs 0x800` accelerator call, which is an in-place memory effect, not a
    control transfer, so `kssCr` covers every address the routine executes. -/
abbrev kssCr : CodeReq := CodeReq.ofProg KssB kssProgL

/-- Singleton code fact at program index `k` is implied by `kssCr`. -/
theorem kss_mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = KssB + BitVec.ofNat 64 (4 * k))
    (hk : k < kssProgL.length)
    (hins : kssProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → kssCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at KssB A kssProgL k ins hA hk hins kssProgL_bound a i h

/-- The saved-register frame: `ra` plus seven callee-saved registers. -/
def kssFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24),
   (.x19, 32), (.x20, 40), (.x21, 48), (.x22, 56)]

/-- The 51-instruction body between prologue and epilogue. -/
def kssBody : List Instr := (kssProgL.drop 9).take 51

theorem kssBody_len : kssBody.length = 51 := by decide

/-- **Structural drift guard.** The emitted routine IS the ABI-frame flatten —
    so the prologue/epilogue contract is DERIVED via `abiFrame_spec_own`, never
    assumed. Kernel-checked by `decide`, so a re-emit that changes the frame
    breaks the build rather than silently invalidating the triple. -/
theorem kssProg_eq_abiFrame :
    abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) kssFrame kssBody = kssProgL := by
  decide

theorem kssFrame_len : kssFrame.length = 8 := by decide

/-- Body entry PC: `KssB + 4 * (1 + |kssFrame|)`. -/
theorem kssBodyEntry_eq : KssB + BitVec.ofNat 64 (4 * (1 + kssFrame.length)) = KssB + 36 := by
  decide

/-- Body exit PC: `KssB + 4 * (1 + |kssFrame| + |kssBody|)`. -/
theorem kssBodyExit_eq :
    KssB + BitVec.ofNat 64 (4 * (1 + kssFrame.length + kssBody.length)) = KssB + 240 := by
  decide

/-! ## `la s3, zk3_state` — the layout bridge at index 12 (`KssB + 48`) -/

theorem kss_la_hi :
    Codegen.laHi GuestAddrs.zk3_state (GuestAddrs.zkvm_keccak256_segments + 48) =
      Rv64.laHi (KssB + 48) KssZk3 := by
  decide

theorem kss_la_lo :
    Codegen.laLo GuestAddrs.zk3_state (GuestAddrs.zkvm_keccak256_segments + 48) =
      Rv64.laLo (KssB + 48) KssZk3 := by
  decide

theorem kss_la_range : laInRange (KssB + 48) KssZk3 := by decide

/-! ## Setup: body entry (`KssB+36`) → outer loop head (`KssB+84`) -/

/-- The three ABI moves: `s0 := a0` (descriptor base), `s1 := a1` (count),
    `s2 := a2` (32-byte output pointer). `KssB+36 → KssB+48`. -/
theorem kssSetupMoves_spec (segsBase nsegsW outputBase : Word)
    (v8 v9 v18 : Word) :
    cpsTripleWithin 3 (KssB + 36) (KssB + 48) kssCr
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ nsegsW) ** (.x18 ↦ᵣ outputBase)) := by
  have h0 := mv_spec_gen_within .x8 .x10 segsBase v8 (KssB + 36) (by decide)
  rw [show (KssB + 36 : Word) + 4 = KssB + 40 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (kss_mem_at 9 (.MV .x8 .x10) (KssB + 36) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl)) h0
  have h0F := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18)) (by pcf) l0
  have c0 : cpsTripleWithin 1 (KssB + 36) (KssB + 40) kssCr
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := mv_spec_gen_within .x9 .x11 nsegsW v9 (KssB + 40) (by decide)
  rw [show (KssB + 40 : Word) + 4 = KssB + 44 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (kss_mem_at 10 (.MV .x9 .x11) (KssB + 40) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl)) h1
  have h1F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ segsBase) ** (.x12 ↦ᵣ outputBase) **
      (.x8 ↦ᵣ segsBase) ** (.x18 ↦ᵣ v18)) (by pcf) l1
  have c1 : cpsTripleWithin 1 (KssB + 40) (KssB + 44) kssCr
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ nsegsW) ** (.x18 ↦ᵣ v18)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have h2 := mv_spec_gen_within .x18 .x12 outputBase v18 (KssB + 44) (by decide)
  rw [show (KssB + 44 : Word) + 4 = KssB + 48 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (kss_mem_at 11 (.MV .x18 .x12) (KssB + 44) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl)) h2
  have h2F := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ nsegsW)) (by pcf) l2
  have c2 : cpsTripleWithin 1 (KssB + 44) (KssB + 48) kssCr
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ nsegsW) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ nsegsW) ** (.x12 ↦ᵣ outputBase) **
        (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ nsegsW) ** (.x18 ↦ᵣ outputBase)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-- `la s3, zk3_state` at `KssB+48` (AUIPC/ADDI pair). `KssB+48 → KssB+56`. -/
theorem kssSetupLa_spec (v19 : Word) :
    cpsTripleWithin 2 (KssB + 48) (KssB + 56) kssCr
      (.x19 ↦ᵣ v19) (.x19 ↦ᵣ KssZk3) := by
  have hau : ∀ a i,
      CodeReq.singleton (KssB + 48)
        (.AUIPC .x19 (Rv64.laHi (KssB + 48) KssZk3)) a = some i →
        kssCr a = some i := by
    intro a i hi
    have hmem := kss_mem_at 12
      (.AUIPC .x19 (Codegen.laHi GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256_segments + 48)))
      (KssB + 48) (by decide) (by rw [kssProgL_len]; decide) (by rfl)
    exact hmem a i (by rwa [← kss_la_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((KssB + 48) + 4)
        (.ADDI .x19 .x19 (Rv64.laLo (KssB + 48) KssZk3)) a = some i →
        kssCr a = some i := by
    intro a i hi
    have hmem := kss_mem_at 13
      (.ADDI .x19 .x19 (Codegen.laLo GuestAddrs.zk3_state
        (GuestAddrs.zkvm_keccak256_segments + 48)))
      (KssB + 52) (by decide) (by rw [kssProgL_len]; decide) (by rfl)
    have hpc : (KssB + 48 : Word) + 4 = KssB + 52 := by decide
    rw [hpc, ← kss_la_lo] at hi
    exact hmem a i hi
  have h := la_materialize_within .x19 v19 (KssB + 48) KssZk3
    (by decide) kss_la_range hau had
  rwa [show (KssB + 48 : Word) + 8 = KssB + 56 from by decide] at h

/-- Zero-loop prep: `mv t0,s3; li t1,25`. `KssB+56 → KssB+64`. -/
theorem kssSetupZeroPrep_spec (v5 v6 : Word) :
    cpsTripleWithin 2 (KssB + 56) (KssB + 64) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x19 ↦ᵣ KssZk3) ** (.x5 ↦ᵣ KssZk3) ** (.x6 ↦ᵣ BitVec.ofNat 64 25)) := by
  have h0 := mv_spec_gen_within .x5 .x19 KssZk3 v5 (KssB + 56) (by decide)
  rw [show (KssB + 56 : Word) + 4 = KssB + 60 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (kss_mem_at 14 (.MV .x5 .x19) (KssB + 56) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl)) h0
  have h0F := cpsTripleWithin_frameR (.x6 ↦ᵣ v6) (by pcf) l0
  have c0 : cpsTripleWithin 1 (KssB + 56) (KssB + 60) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x19 ↦ᵣ KssZk3) ** (.x5 ↦ᵣ KssZk3) ** (.x6 ↦ᵣ v6)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h0F
  have h1 := li_spec_gen_within .x6 v6 (BitVec.ofNat 64 25) (KssB + 60) (by decide)
  rw [show (KssB + 60 : Word) + 4 = KssB + 64 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (kss_mem_at 15 (.LI .x6 (BitVec.ofNat 64 25)) (KssB + 60) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl)) h1
  have h1F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ KssZk3) ** (.x5 ↦ᵣ KssZk3)) (by pcf) l1
  have c1 : cpsTripleWithin 1 (KssB + 60) (KssB + 64) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x5 ↦ᵣ KssZk3) ** (.x6 ↦ᵣ v6))
      ((.x19 ↦ᵣ KssZk3) ** (.x5 ↦ᵣ KssZk3) ** (.x6 ↦ᵣ BitVec.ofNat 64 25)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- The 25-dword sponge zeroing loop, `KssB+64 → KssB+80`. Reuses the
    register-generic `keccakZeroLoop_spec` with cursor `t0` and counter `t1`. -/
theorem kssZeroLoop_spec (os : List (BitVec 8))
    (hlen : os.length = 200)
    (halign : KssZk3.toNat % 8 = 0)
    (hover : KssZk3.toNat + 200 < 2 ^ 64) :
    cpsTripleWithin 100 (KssB + 64) (KssB + 80) kssCr
      ((.x5 ↦ᵣ KssZk3) ** (.x6 ↦ᵣ BitVec.ofNat 64 25) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion KssZk3 os)
      ((.x5 ↦ᵣ (KssZk3 + BitVec.ofNat 64 200)) ** (.x6 ↦ᵣ BitVec.ofNat 64 0) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion KssZk3 keccakZeroStateBytes) := by
  have hloop := keccakZeroLoop_spec kssCr (KssB + 64) .x5 .x6 KssZk3 os
    (by decide) (by decide) hlen halign hover
    (kss_mem_at 16 (.SD .x5 .x0 0) (KssB + 64) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (kss_mem_at 17 (.ADDI .x5 .x5 (8 : BitVec 12)) (KssB + 68) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (kss_mem_at 18 (.ADDI .x6 .x6 (-1 : BitVec 12)) (KssB + 72) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (kss_mem_at 19 (.BNE .x6 .x0 (-12 : BitVec 13)) (KssB + 76) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
  rw [show (KssB + 64 : Word) + 16 = KssB + 80 from by decide] at hloop
  exact cpsTripleWithin_mono_nSteps (by omega) hloop

/-- `li s4, 0` — the rate-block fill offset starts at 0. `KssB+80 → KssB+84`. -/
theorem kssFillInit_spec (v20 : Word) :
    cpsTripleWithin 1 (KssB + 80) (KssB + 84) kssCr
      (.x20 ↦ᵣ v20) (.x20 ↦ᵣ (BitVec.ofNat 64 0)) := by
  have h1 := li_spec_gen_within .x20 v20 (BitVec.ofNat 64 0) (KssB + 80) (by decide)
  rw [show (KssB + 80 : Word) + 4 = KssB + 84 from by decide] at h1
  exact cpsTripleWithin_extend_code
    (kss_mem_at 20 (.LI .x20 (BitVec.ofNat 64 0)) (KssB + 80) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl)) h1

end EvmAsm.Codegen.Proofs
