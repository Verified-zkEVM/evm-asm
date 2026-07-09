/-
  EvmAsm.Evm64.Terminating.ReturnWindowLoopSpec

  The three loops of the standalone (`depthAware = false`) `RETURN` (0xf3) /
  `REVERT` (0xfd) return-data descriptor window that precedes the shared halt
  core (`ReturnHaltProgram`/`ReturnHaltSpec`):

  1. `returnZeroLoop` — the 22-word descriptor-body zeroing loop
     (`sd x0, 0(x19)` countdown, `descriptor+72 .. descriptor+248`).
  2. `returnCopyLoop` — the `evm_memory[offset .. offset+clamped]` → descriptor
     byte-copy loop (no zero-fill; the clamp bounds the source in range).
  3. reused by the first-32-byte prefix copy (same loop program).

  Each loop is proved `∀ base` over its own standalone `Program` slice by
  induction on the byte / word countdown, mirroring the CODECOPY copy-loop
  (`Evm64/Code/CopyLoopSpec.lean`) and TLOAD reverse-scan styles.  The pure
  descriptor-content models are `zeroDwords` (a run of zeroed dwords) and a
  reuse of `bytesRegion`'s `List.set` byte writes.

  Also here: `bytesRegion_sd_within`, the dword-store analog of
  `bytesRegion_sb_within` (`Rv64/MemRegionStore.lean`) — an `SD` into a
  dword-aligned slot of a `bytesRegion`, turning the region byte-list into
  `setBytes bs (8*q) (dwordBytes v)`.

  Kernel-checkable throughout (classical-3 only): no `native_decide` /
  `bv_decide`.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.MemRegionWriteWide
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPermChunked

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

/-! ## `SD` into a `bytesRegion` (the dword-store analog of `bytesRegion_sb_within`) -/

/-- **`SD` with an immediate offset writes the dword at slot `q` of the region.**
    Storing `rs2`'s word at `regionBase + off` where `signExtend12 off = 8*q`
    (`8*q + 8 ≤ bs.length`) turns `bytesRegion regionBase bs` into
    `bytesRegion regionBase (setBytes bs (8*q) (dwordBytes v_data))`.  The base
    register holds `regionBase` and the dword slot is selected by the *instruction*
    offset — the shape the descriptor header / size / clamped stores use
    (`sd x0, 8(x16)`, `sd x15, 64(x16)`, `sd x21, 248(x16)`, …). -/
theorem bytesRegion_sd_off_within (rs1 rs2 : Reg) (regionBase v_data : Word) (base : Word)
    (bs : List (BitVec 8)) (q : Nat) (off : BitVec 12)
    (hoff : signExtend12 off = BitVec.ofNat 64 (8 * q))
    (hi : 8 * q + 8 ≤ bs.length) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD rs1 rs2 off))
      ((rs1 ↦ᵣ regionBase) ** (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ regionBase) ** (rs2 ↦ᵣ v_data) **
        bytesRegion regionBase (setBytes bs (8 * q) (dwordBytes v_data))) := by
  set chunk := (bs.drop (8 * q)).take 8 with hchunk
  have hclen : 8 ≤ chunk.length := by
    rw [hchunk, List.length_take, List.length_drop]; omega
  obtain ⟨front, rest, hf, hr, heq, heqset⟩ :=
    bytesRegion_dword_at_setBytes regionBase bs (dwordBytes v_data) q 0
      (by simp [dwordBytes]) (by simp) (by simpa using hi)
  rw [Nat.add_zero] at heqset
  have hsd := generic_sd_spec_within rs1 rs2 regionBase v_data (packBytes chunk) off base
  rw [hoff] at hsd
  rw [heq, heqset, ← hchunk, ← packBytes_setBytes_dword chunk v_data hclen]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) hsd)

/-- **`SD` writes the dword at slot `q` of the region.** Storing `rs2`'s word at
    `regionBase + 8*q` (`8*q + 8 ≤ bs.length`, base dword-aligned implied by the
    region cells) turns `bytesRegion regionBase bs` into
    `bytesRegion regionBase (setBytes bs (8*q) (dwordBytes v_data))` — the word
    store a descriptor-zeroing / header loop needs. -/
theorem bytesRegion_sd_within (rs1 rs2 : Reg) (regionBase v_data : Word) (base : Word)
    (bs : List (BitVec 8)) (q : Nat)
    (hi : 8 * q + 8 ≤ bs.length) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD rs1 rs2 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q))) ** (rs2 ↦ᵣ v_data) **
        bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q))) ** (rs2 ↦ᵣ v_data) **
        bytesRegion regionBase (setBytes bs (8 * q) (dwordBytes v_data))) := by
  set chunk := (bs.drop (8 * q)).take 8 with hchunk
  have hclen : 8 ≤ chunk.length := by
    rw [hchunk, List.length_take, List.length_drop]; omega
  obtain ⟨front, rest, hf, hr, heq, heqset⟩ :=
    bytesRegion_dword_at_setBytes regionBase bs (dwordBytes v_data) q 0
      (by simp [dwordBytes]) (by simp) (by simpa using hi)
  rw [Nat.add_zero] at heqset
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * q) with hdwa
  have hsd := generic_sd_spec_within rs1 rs2 dwordAddr v_data (packBytes chunk)
    (0 : BitVec 12) base
  rw [show dwordAddr + signExtend12 (0 : BitVec 12) = dwordAddr from by
        rw [signExtend12_0]; bv_omega] at hsd
  rw [heq, heqset, ← hchunk, ← packBytes_setBytes_dword chunk v_data hclen]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) hsd)

end EvmAsm.Rv64

namespace EvmAsm.Evm64
namespace Terminating

open EvmAsm.Rv64

/-- `pcFree` extended to close `bytesRegion _.pcFree` leaves. -/
local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | apply pcFree_sepConj
    | pcFree)

/-! ## Word-counter arithmetic (loop decrement / nonzero) -/

/-- `(n+1) - 1 = n` as words (loop counter decrement). -/
private theorem rw_word_succ_dec (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hs : (signExtend12 (-1 : BitVec 12) : Word).toNat = 18446744073709551615 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A successor counter `< 2^64` is nonzero as a word. -/
private theorem rw_word_succ_ne_zero (n : Nat) (h : n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (n + 1) ≠ (0 : Word) := by
  have ht : (BitVec.ofNat 64 (n + 1) : Word).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat]; omega
  intro hc; rw [hc] at ht; simp at ht

/-! ## The descriptor-body zeroing loop -/

/-- The 5-instruction zeroing loop (`.L1` … `.L2` of `returnRevertTail`):
    ```
    1: beqz x21, 2f      -- BEQ x21 x0 (+20)
       sd x0, 0(x19)     -- SD x19 x0 0
       addi x19, x19, 8
       addi x21, x21, -1
       j 1b              -- JAL x0 (-16)
    2:
    ``` -/
def returnZeroLoop : Program :=
  [.BEQ .x21 .x0 (BitVec.ofNat 13 20),
   .SD .x19 .x0 0,
   .ADDI .x19 .x19 8,
   .ADDI .x21 .x21 (-1 : BitVec 12),
   .JAL .x0 (-16 : BitVec 21)]

@[simp] theorem returnZeroLoop_length : returnZeroLoop.length = 5 := rfl

/-- Zero the `i` dwords `[q0, q0 + i)` of a region byte-list (forward, matching
    the loop's advancing pointer). -/
def zeroDwords (bs : List (BitVec 8)) (q0 : Nat) : Nat → List (BitVec 8)
  | 0 => bs
  | (i + 1) => setBytes (zeroDwords bs q0 i) (8 * (q0 + i)) (dwordBytes (0 : Word))

@[simp] theorem zeroDwords_length (bs : List (BitVec 8)) (q0 i : Nat) :
    (zeroDwords bs q0 i).length = bs.length := by
  induction i with
  | zero => rfl
  | succ k ih => simp only [zeroDwords, length_setBytes, ih]

/-- Pointer advance by 8 bytes: `descBase + 8*m` then `+8` is `descBase + 8*(m+1)`. -/
private theorem zl_advance (descBase : Word) (m : Nat) :
    (descBase + BitVec.ofNat 64 (8 * m)) + signExtend12 (8 : BitVec 12)
      = descBase + BitVec.ofNat 64 (8 * (m + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega

/-- **The descriptor-body zeroing loop closure** (`base → base+20`) by induction
    on the word countdown `n`.  Entering with `n` dwords left and `i` already
    zeroed (`x21 = n`, `x19 = descBase + 8*(q0+i)`, region `zeroDwords bs q0 i`),
    it zeroes the remaining `n` dwords, leaving `x21 = 0`,
    `x19 = descBase + 8*(q0+i+n)`, region `zeroDwords bs q0 (i+n)`. -/
theorem returnZeroLoop_spec_within (base descBase : Word) (bs : List (BitVec 8))
    (q0 n i : Nat)
    (hlen : 8 * (q0 + i + n) ≤ bs.length)
    (hbs : bs.length < 2 ^ 64) :
    cpsTripleWithin (5 * n + 1) base (base + 20)
      (CodeReq.ofProg base returnZeroLoop)
      (((.x21 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (8 * (q0 + i)))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion descBase (zeroDwords bs q0 i))
      (((.x21 : Reg) ↦ᵣ (0 : Word)) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (8 * (q0 + i + n)))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion descBase (zeroDwords bs q0 (i + n))) := by
  -- Code-inclusion (mono) lemmas for the five loop instructions.
  have hmono0 : ∀ a i', CodeReq.singleton base (.BEQ .x21 .x0 (BitVec.ofNat 13 20)) a = some i'
      → CodeReq.ofProg base returnZeroLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnZeroLoop 0 base
      (by decide) (by decide) (by bv_omega))
  have hmono1 : ∀ a i', CodeReq.singleton (base + 4) (.SD .x19 .x0 0) a = some i'
      → CodeReq.ofProg base returnZeroLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnZeroLoop 1 (base + 4)
      (by decide) (by decide) (by bv_omega))
  have hmono2 : ∀ a i', CodeReq.singleton (base + 8) (.ADDI .x19 .x19 8) a = some i'
      → CodeReq.ofProg base returnZeroLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnZeroLoop 2 (base + 8)
      (by decide) (by decide) (by bv_omega))
  have hmono3 : ∀ a i', CodeReq.singleton (base + 12) (.ADDI .x21 .x21 (-1 : BitVec 12)) a = some i'
      → CodeReq.ofProg base returnZeroLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnZeroLoop 3 (base + 12)
      (by decide) (by decide) (by bv_omega))
  have hmono4 : ∀ a i', CodeReq.singleton (base + 16) (.JAL .x0 (-16 : BitVec 21)) a = some i'
      → CodeReq.ofProg base returnZeroLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnZeroLoop 4 (base + 16)
      (by decide) (by decide) (by bv_omega))
  have ha_t : base + signExtend13 (BitVec.ofNat 13 20) = base + 20 := by
    rw [show signExtend13 (BitVec.ofNat 13 20) = (20 : Word) from by decide]
  have ha_f : base + signExtend13 (BitVec.ofNat 13 20) = base + 20 := ha_t
  have ha_back : (base + 16) + signExtend21 (-16 : BitVec 21) = base := by
    rw [show signExtend21 (-16 : BitVec 21) = (-16 : Word) from by decide]; bv_omega
  induction n generalizing i with
  | zero =>
    -- x21 = 0 → beqz taken → exit at base+20.
    have hbeq := beq_spec_gen_within .x21 .x0 (BitVec.ofNat 13 20) (BitVec.ofNat 64 0)
      (0 : Word) base
    rw [ha_t] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (8 * (q0 + i)))) **
       bytesRegion descBase (zeroDwords bs q0 i)) (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          simp only [Nat.add_zero]
          xperm_chunked hq) htf)
  | succ k ih =>
    have hle : k + 1 ≤ 8 * (q0 + i + (k + 1)) := by omega
    -- Step 0: BEQ not taken (x21 = k+1 ≠ 0).
    have hbeq := beq_spec_gen_within .x21 .x0 (BitVec.ofNat 13 20) (BitVec.ofNat 64 (k + 1))
      (0 : Word) base
    rw [ha_f] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact rw_word_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (8 * (q0 + i)))) **
       bytesRegion descBase (zeroDwords bs q0 i)) (by pcFreeR) hnt
    -- Step 1: SD x0 at x19 (dword q0+i of the region).
    have hsd := bytesRegion_sd_within .x19 .x0 descBase (0 : Word) (base + 4)
      (zeroDwords bs q0 i) (q0 + i) (by rw [zeroDwords_length]; omega)
    have hsde := cpsTripleWithin_extend_code hmono1 hsd
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hsde
    have hsdf := cpsTripleWithin_frameR ((.x21 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1))
      (by pcFreeR) hsde
    -- Step 2: ADDI x19 += 8.
    have h2 := addi_spec_gen_same_within .x19
      (descBase + BitVec.ofNat 64 (8 * (q0 + i))) (8 : BitVec 12) (base + 8) (by decide)
    rw [zl_advance descBase (q0 + i),
        show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at h2
    have h2e := cpsTripleWithin_extend_code hmono2 h2
    have h2f := cpsTripleWithin_frameR
      (((.x21 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion descBase (zeroDwords bs q0 (i + 1))) (by pcFreeR) h2e
    -- Step 3: ADDI x21 -= 1.
    have h3 := addi_spec_gen_same_within .x21 (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12)
      (base + 12) (by decide)
    rw [rw_word_succ_dec k, show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at h3
    have h3e := cpsTripleWithin_extend_code hmono3 h3
    have h3f := cpsTripleWithin_frameR
      (((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (8 * (q0 + i + 1)))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion descBase (zeroDwords bs q0 (i + 1))) (by pcFreeR) h3e
    -- Step 4: JAL back to base.
    have h4 := jal_x0_spec_gen_within (-16 : BitVec 21) (base + 16)
    rw [ha_back] at h4
    have h4e := cpsTripleWithin_extend_code hmono4 h4
    have h4f := cpsTripleWithin_frameR
      (((.x21 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (8 * (q0 + i + 1)))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion descBase (zeroDwords bs q0 (i + 1))) (by pcFreeR) h4e
    -- IH at i+1, n=k.
    have hih := ih (i + 1) (by rw [show q0 + (i + 1) + k = q0 + i + (k + 1) from by omega]; exact hlen)
    -- The region after the SD is `zeroDwords bs q0 (i+1)` (definitional).
    have hset_eq : setBytes (zeroDwords bs q0 i) (8 * (q0 + i)) (dwordBytes (0 : Word))
        = zeroDwords bs q0 (i + 1) := rfl
    rw [hset_eq] at hsdf
    -- Address bridge: 8*(q0 + (i+1)) = 8*(q0+i+1) and i+1+k = i+(k+1).
    have haddr1 : q0 + (i + 1) = q0 + i + 1 := by omega
    -- Compose the five body steps, then the IH.
    have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hsdf
    have s012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s01 h2f
    have s0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s012 h3f
    have s01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left']; xperm_chunked hp) s0123 h4f
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left'] at hp
      rw [← haddr1] at hp; xperm_chunked hp) s01234 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show q0 + (i + 1) + k = q0 + i + (k + 1) from by omega,
                     show i + 1 + k = i + (k + 1) from by omega] at hq
          xperm_chunked hq) sfull)

/-! ## The `evm_memory → descriptor` byte-copy loop -/

/-- The 7-instruction copy loop (`.L4`/`.L7` of `returnRevertTail`):
    ```
    4: beqz x22, 5f      -- BEQ x22 x0 (+28)
       lbu x23, 0(x17)   -- LBU x23 x17 0
       sb  x23, 0(x19)   -- SB  x19 x23 0
       addi x17, x17, 1
       addi x19, x19, 1
       addi x22, x22, -1
       j 4b              -- JAL x0 (-24)
    5:
    ```
    A pure byte copy `src → dest`; the size is clamped in range so there is no
    zero-fill (unlike CODECOPY's copy loop). -/
def returnCopyLoop : Program :=
  [.BEQ .x22 .x0 (BitVec.ofNat 13 28),
   .LBU .x23 .x17 0,
   .SB .x19 .x23 0,
   .ADDI .x17 .x17 1,
   .ADDI .x19 .x19 1,
   .ADDI .x22 .x22 (-1 : BitVec 12),
   .JAL .x0 (-24 : BitVec 21)]

@[simp] theorem returnCopyLoop_length : returnCopyLoop.length = 7 := rfl

/-- Copy `i` bytes of `srcBytes` (from `srcOff`) into `destBytes` (at `destOff`),
    forward, matching the loop's advancing pointers. -/
def copyIntoRegion (destBytes srcBytes : List (BitVec 8)) (destOff srcOff : Nat) :
    Nat → List (BitVec 8)
  | 0 => destBytes
  | (i + 1) =>
      (copyIntoRegion destBytes srcBytes destOff srcOff i).set (destOff + i)
        (srcBytes.getD (srcOff + i) 0)

@[simp] theorem copyIntoRegion_length (destBytes srcBytes : List (BitVec 8))
    (destOff srcOff i : Nat) :
    (copyIntoRegion destBytes srcBytes destOff srcOff i).length = destBytes.length := by
  induction i with
  | zero => rfl
  | succ k ih => simp only [copyIntoRegion, List.length_set, ih]

/-- Pointer advance by 1 byte. -/
private theorem cl_advance (b : Word) (m : Nat) :
    (b + BitVec.ofNat 64 m) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (m + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega

/-- **The `evm_memory → descriptor` copy-loop closure** (`base → base+28`) by
    induction on the byte countdown `n`.  Entering with `n` bytes left and `i`
    copied, it copies the remaining `n` bytes, advancing `x17`/`x19` by `n` and
    zeroing `x22`; the destination region gains `copyIntoRegion … (i+n)`. -/
theorem returnCopyLoop_spec_within (base srcBase descBase : Word)
    (srcBytes destBytes : List (BitVec 8)) (srcOff destOff n i : Nat) (x23old : Word)
    (h_src_align : srcBase.toNat % 8 = 0)
    (h_dest_align : descBase.toNat % 8 = 0)
    (h_src_bound : srcOff + i + n ≤ srcBytes.length)
    (h_dest_bound : destOff + i + n ≤ destBytes.length)
    (h_src_over : srcBase.toNat + srcBytes.length < 2 ^ 64)
    (h_dest_over : descBase.toNat + destBytes.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < srcBytes.length →
      isValidByteAccess (srcBase + BitVec.ofNat 64 k) = true)
    (h_dest_valid : ∀ k, k < destBytes.length →
      isValidByteAccess (descBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * n + 1) base (base + 28)
      (CodeReq.ofProg base returnCopyLoop)
      (((.x22 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x23 : Reg) ↦ᵣ x23old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (((.x22 : Reg) ↦ᵣ (0 : Word)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i + n))) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + i + n))) **
       regOwn .x23 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + n))) := by
  have hmono0 : ∀ a i', CodeReq.singleton base (.BEQ .x22 .x0 (BitVec.ofNat 13 28)) a = some i'
      → CodeReq.ofProg base returnCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCopyLoop 0 base
      (by decide) (by decide) (by bv_omega))
  have hmono1 : ∀ a i', CodeReq.singleton (base + 4) (.LBU .x23 .x17 0) a = some i'
      → CodeReq.ofProg base returnCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCopyLoop 1 (base + 4)
      (by decide) (by decide) (by bv_omega))
  have hmono2 : ∀ a i', CodeReq.singleton (base + 8) (.SB .x19 .x23 0) a = some i'
      → CodeReq.ofProg base returnCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCopyLoop 2 (base + 8)
      (by decide) (by decide) (by bv_omega))
  have hmono3 : ∀ a i', CodeReq.singleton (base + 12) (.ADDI .x17 .x17 1) a = some i'
      → CodeReq.ofProg base returnCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCopyLoop 3 (base + 12)
      (by decide) (by decide) (by bv_omega))
  have hmono4 : ∀ a i', CodeReq.singleton (base + 16) (.ADDI .x19 .x19 1) a = some i'
      → CodeReq.ofProg base returnCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCopyLoop 4 (base + 16)
      (by decide) (by decide) (by bv_omega))
  have hmono5 : ∀ a i', CodeReq.singleton (base + 20) (.ADDI .x22 .x22 (-1 : BitVec 12)) a = some i'
      → CodeReq.ofProg base returnCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCopyLoop 5 (base + 20)
      (by decide) (by decide) (by bv_omega))
  have hmono6 : ∀ a i', CodeReq.singleton (base + 24) (.JAL .x0 (-24 : BitVec 21)) a = some i'
      → CodeReq.ofProg base returnCopyLoop a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base returnCopyLoop 6 (base + 24)
      (by decide) (by decide) (by bv_omega))
  have ha_t : base + signExtend13 (BitVec.ofNat 13 28) = base + 28 := by
    rw [show signExtend13 (BitVec.ofNat 13 28) = (28 : Word) from by decide]
  have ha_back : (base + 24) + signExtend21 (-24 : BitVec 21) = base := by
    rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
  induction n generalizing i x23old with
  | zero =>
    have hbeq := beq_spec_gen_within .x22 .x0 (BitVec.ofNat 13 28) (BitVec.ofNat 64 0)
      (0 : Word) base
    rw [ha_t] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have htaken := cpsBranchWithin_takenStripPure2 hbeqe (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact ((sepConj_pure_right _).1 hQ).2 (by decide))
    have htf := cpsTripleWithin_frameR
      (((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x23 : Reg) ↦ᵣ x23old) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (by pcFreeR) htaken
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun sState hq => by
          rw [show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hq
          simp only [Nat.add_zero]
          have hq2 : (((.x23 : Reg) ↦ᵣ x23old) **
              ((.x22 : Reg) ↦ᵣ (0 : Word)) **
              ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
              ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + i))) **
              ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion srcBase srcBytes **
              bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff i)) sState := by
            xperm_chunked hq
          have hq3 := sepConj_mono_left (regIs_implies_regOwn .x23) _ hq2
          xperm_chunked hq3) htf)
  | succ k ih =>
    have hsi : srcOff + i < srcBytes.length := by omega
    have hdi : destOff + i < destBytes.length := by omega
    set bval := srcBytes[srcOff + i]'hsi with hbval
    have htrunc : (bval.zeroExtend 64).truncate 8 = bval := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
      have := bval.isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hgetd : srcBytes.getD (srcOff + i) 0 = bval := by
      rw [hbval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsi]; rfl
    have hstep : copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)
        = (copyIntoRegion destBytes srcBytes destOff srcOff i).set (destOff + i) bval := by
      simp only [copyIntoRegion, hgetd]
    -- Step 0: BEQ not taken (x22 = k+1 ≠ 0).
    have hbeq := beq_spec_gen_within .x22 .x0 (BitVec.ofNat 13 28) (BitVec.ofNat 64 (k + 1))
      (0 : Word) base
    rw [ha_t] at hbeq
    have hbeqe := cpsBranchWithin_extend_code hmono0 hbeq
    have hnt := cpsBranchWithin_ntakenStripPure2 hbeqe (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact rw_word_succ_ne_zero k (by omega) ((sepConj_pure_right _).1 hQ).2)
    have hntf := cpsTripleWithin_frameR
      (((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x23 : Reg) ↦ᵣ x23old) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (by pcFreeR) hnt
    -- Step 1: LBU x23 ← src[srcOff+i].
    have hlbu := bytesRegion_lbu_within .x23 .x17 srcBase x23old (base + 4)
      srcBytes (srcOff + i) (by decide) h_src_align hsi (by omega)
      (h_src_valid (srcOff + i) hsi)
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega, ← hbval] at hlbu
    have hlbue := cpsTripleWithin_extend_code hmono1 hlbu
    have hlbuf := cpsTripleWithin_frameR
      (((.x22 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff i))
      (by pcFreeR) hlbue
    -- Step 2: SB dest[destOff+i] ← x23 (= bval).
    have hsb := bytesRegion_sb_within .x19 .x23 descBase (bval.zeroExtend 64) (base + 8)
      (copyIntoRegion destBytes srcBytes destOff srcOff i) (destOff + i) h_dest_align
      (by rw [copyIntoRegion_length]; omega) (by omega)
      (h_dest_valid (destOff + i) hdi)
    rw [htrunc, ← hstep, show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hsb
    have hsbe := cpsTripleWithin_extend_code hmono2 hsb
    have hsbf := cpsTripleWithin_frameR
      (((.x22 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + i))) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes)
      (by pcFreeR) hsbe
    -- Step 3: ADDI x17 += 1.
    have h3 := addi_spec_gen_same_within .x17
      (srcBase + BitVec.ofNat 64 (srcOff + i)) (1 : BitVec 12) (base + 12) (by decide)
    rw [cl_advance srcBase (srcOff + i),
        show srcOff + i + 1 = srcOff + (i + 1) from by omega,
        show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at h3
    have h3e := cpsTripleWithin_extend_code hmono3 h3
    have h3f := cpsTripleWithin_frameR
      (((.x22 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + i))) **
       ((.x23 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h3e
    -- Step 4: ADDI x19 += 1.
    have h4 := addi_spec_gen_same_within .x19
      (descBase + BitVec.ofNat 64 (destOff + i)) (1 : BitVec 12) (base + 16) (by decide)
    rw [cl_advance descBase (destOff + i),
        show destOff + i + 1 = destOff + (i + 1) from by omega,
        show (base + 16 : Word) + 4 = base + 20 from by bv_omega] at h4
    have h4e := cpsTripleWithin_extend_code hmono4 h4
    have h4f := cpsTripleWithin_frameR
      (((.x22 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x23 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h4e
    -- Step 5: ADDI x22 -= 1.
    have h5 := addi_spec_gen_same_within .x22 (BitVec.ofNat 64 (k + 1)) (-1 : BitVec 12)
      (base + 20) (by decide)
    rw [rw_word_succ_dec k, show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at h5
    have h5e := cpsTripleWithin_extend_code hmono5 h5
    have h5f := cpsTripleWithin_frameR
      (((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       ((.x23 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h5e
    -- Step 6: JAL back to base.
    have h6 := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 24)
    rw [ha_back] at h6
    have h6e := cpsTripleWithin_extend_code hmono6 h6
    have h6f := cpsTripleWithin_frameR
      (((.x22 : Reg) ↦ᵣ BitVec.ofNat 64 k) **
       ((.x17 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (srcOff + (i + 1)))) **
       ((.x19 : Reg) ↦ᵣ (descBase + BitVec.ofNat 64 (destOff + (i + 1)))) **
       ((.x23 : Reg) ↦ᵣ (bval.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion descBase (copyIntoRegion destBytes srcBytes destOff srcOff (i + 1)))
      (by pcFreeR) h6e
    have hih := ih (i + 1) (bval.zeroExtend 64)
      (by rw [show srcOff + (i + 1) + k = srcOff + i + (k + 1) from by omega]; exact h_src_bound)
      (by rw [show destOff + (i + 1) + k = destOff + i + (k + 1) from by omega]; exact h_dest_bound)
    -- Compose.
    have s01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hntf hlbuf
    have s012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s01 hsbf
    have s0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s012 h3f
    have s01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s0123 h4f
    have s012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s01234 h5f
    have s0_6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left']; xperm_chunked hp) s012345 h6f
    have sfull := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [sepConj_emp_left'] at hp
      xperm_chunked hp) s0_6 hih
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
        (fun _ hq => by
          simp only [show srcOff + (i + 1) + k = srcOff + i + (k + 1) from by omega,
                     show destOff + (i + 1) + k = destOff + i + (k + 1) from by omega,
                     show i + 1 + k = i + (k + 1) from by omega] at hq
          xperm_chunked hq) sfull)

end Terminating
end EvmAsm.Evm64
