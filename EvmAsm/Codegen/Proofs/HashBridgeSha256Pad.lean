/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Pad

  Pad-path first slice for `zkvm_sha256`: one-dword
  `SD x21, x0, 8q` zero of the 64-byte scratch at `B+4*(49+q)` (prog idx 49-56).
  8× compose + remainder/0x80/bitlen/final CSRS/BE squeeze remain.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256OuterBody
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]
  norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins
    sha256ProgL_bound a i h

private theorem pad_zero_ins (q : Nat) (hq : q < 8)
    (hidx : 49 + q < sha256ProgL.length) :
    sha256ProgL[49 + q]'hidx =
      .SD .x21 .x0 (BitVec.ofNat 12 (8 * q)) := by
  match q with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | _ + 8 => omega

/-- Zero one dword of scratch via `SD x21, x0, 8q` (x0 holds 0).
    PC = B + 4*(49+q). -/
theorem sha256PadZeroDword_spec (scratchBase : Word) (scratch : List (BitVec 8))
    (q : Nat) (hscratch : scratch.length = 64) (hq : q < 8) :
    cpsTripleWithin 1 (B + BitVec.ofNat 64 (4 * (49 + q)))
      (B + BitVec.ofNat 64 (4 * (49 + q)) + 4) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase
          (setBytes scratch (8 * q) (dwordBytes (0 : Word)))) := by
  have hq_state : 8 * q + 8 ≤ scratch.length := by rw [hscratch]; omega
  have himm : 8 * q < 2 ^ 11 := by omega
  have hidx : 49 + q < sha256ProgL.length := by
    rw [sha256ProgL_len]; omega
  have hins := pad_zero_ins q hq hidx
  have hmem : ∀ a i,
      CodeReq.singleton (B + BitVec.ofNat 64 (4 * (49 + q)))
        (.SD .x21 .x0 (BitVec.ofNat 12 (8 * q))) a = some i →
        sha256Cr a = some i :=
    mem_at (49 + q) (.SD .x21 .x0 (BitVec.ofNat 12 (8 * q)))
      (B + BitVec.ofNat 64 (4 * (49 + q))) rfl hidx hins
  exact cpsTripleWithin_extend_code hmem
    (bytesRegion_sd_within .x21 .x0 scratchBase (0 : Word)
      (B + BitVec.ofNat 64 (4 * (49 + q))) scratch q hq_state himm)

/-- `dwordBytes 0 = replicate 8 0`. -/
theorem dwordBytes_zero :
    dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) := by
  decide

/-- Nested setBytes after 8 zero-dword stores (operational pad-zero post). -/
def sha256PadZeroed (scratch : List (BitVec 8)) : List (BitVec 8) :=
  setBytes (setBytes (setBytes (setBytes (setBytes (setBytes (setBytes
    (setBytes scratch 0 (dwordBytes (0 : Word)))
    8 (dwordBytes (0 : Word)))
    16 (dwordBytes (0 : Word)))
    24 (dwordBytes (0 : Word)))
    32 (dwordBytes (0 : Word)))
    40 (dwordBytes (0 : Word)))
    48 (dwordBytes (0 : Word)))
    56 (dwordBytes (0 : Word))

private theorem pad_zero_pc (q : Nat) (hq : q < 8) :
    B + BitVec.ofNat 64 (4 * (49 + q)) = B + (196 + 4 * q : Nat) := by
  match q with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | _ + 8 => omega

private theorem pad_zero_exit (q : Nat) (hq : q < 8) :
    B + BitVec.ofNat 64 (4 * (49 + q)) + 4 = B + (196 + 4 * (q + 1) : Nat) := by
  have hpc := pad_zero_pc q hq
  have h4 : (B + (196 + 4 * q : Nat) : Word) + 4 = B + (196 + 4 * (q + 1) : Nat) := by
    match q with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | _ + 8 => omega
  rw [hpc, h4]

private theorem pad_step_at (scratchBase : Word) (scratch : List (BitVec 8))
    (q : Nat) (hscratch : scratch.length = 64) (hq : q < 8) :
    cpsTripleWithin 1 (B + (196 + 4 * q : Nat)) (B + (196 + 4 * (q + 1) : Nat))
      sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase
          (setBytes scratch (8 * q) (dwordBytes (0 : Word)))) := by
  have h := sha256PadZeroDword_spec scratchBase scratch q hscratch hq
  have hpc := pad_zero_pc q hq
  have hex := pad_zero_exit q hq
  convert h using 1
  · exact hpc.symm
  · exact hex.symm

/-- Intermediate scratch after first `q` zero-dwords (`q ≤ 8`). -/
def sha256PadZeroedN (scratch : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => scratch
  | q + 1 => setBytes (sha256PadZeroedN scratch q) (8 * q) (dwordBytes (0 : Word))

theorem sha256PadZeroedN_eight (scratch : List (BitVec 8)) :
    sha256PadZeroedN scratch 8 = sha256PadZeroed scratch := by
  simp only [sha256PadZeroedN, sha256PadZeroed]

theorem pad_zeroedN_len (scratch : List (BitVec 8)) (h : scratch.length = 64)
    (q : Nat) : (sha256PadZeroedN scratch q).length = 64 := by
  induction q with
  | zero => simpa [sha256PadZeroedN] using h
  | succ q ih =>
    simp only [sha256PadZeroedN, length_setBytes, ih]

private theorem pad_zero_dword_set (os : List (BitVec 8)) (k : Nat)
    (hk : 8 * k + 8 ≤ os.length) :
    setBytes (List.replicate (8 * k) (0 : BitVec 8) ++ os.drop (8 * k))
        (8 * k) (dwordBytes (0 : Word))
      = List.replicate (8 * (k + 1)) (0 : BitVec 8) ++ os.drop (8 * (k + 1)) := by
  rw [dwordBytes_zero]
  have hleft :
      setBytes (List.replicate (8 * k) (0 : BitVec 8) ++ os.drop (8 * k))
          (8 * k) (List.replicate 8 (0 : BitVec 8))
        = List.replicate (8 * k) (0 : BitVec 8) ++
            setBytes (os.drop (8 * k)) 0 (List.replicate 8 (0 : BitVec 8)) := by
    rw [setBytes_append_right _ _ _ _ (by simp [List.length_replicate])]
    simp only [List.length_replicate, Nat.sub_self]
  rw [hleft]
  have htail :
      setBytes (os.drop (8 * k)) 0 (List.replicate 8 (0 : BitVec 8))
        = List.replicate 8 (0 : BitVec 8) ++ os.drop (8 * (k + 1)) := by
    have hfull :
        setBytes ((os.drop (8 * k)).take 8) 0 (List.replicate 8 (0 : BitVec 8))
          = List.replicate 8 (0 : BitVec 8) := by
      have h := setBytes_dword_full ((os.drop (8 * k)).take 8) (0 : Word)
        (by rw [List.length_take, List.length_drop]; omega)
      rwa [dwordBytes_zero] at h
    have hsplit :
        setBytes (os.drop (8 * k)) 0 (List.replicate 8 (0 : BitVec 8))
          = setBytes ((os.drop (8 * k)).take 8) 0 (List.replicate 8 (0 : BitVec 8))
              ++ (os.drop (8 * k)).drop 8 := by
      have heq : os.drop (8 * k)
          = (os.drop (8 * k)).take 8 ++ (os.drop (8 * k)).drop 8 :=
        (List.take_append_drop 8 (os.drop (8 * k))).symm
      conv_lhs => rw [heq]
      rw [setBytes_append_left _ _ _ _
        (by rw [List.length_take, List.length_drop]; simp; omega)]
    rw [hsplit, hfull, List.drop_drop]
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  rw [htail, ← List.append_assoc, ← List.replicate_add]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem sha256PadZeroedN_spec (scratch : List (BitVec 8)) :
    ∀ q, q ≤ 8 → scratch.length = 64 →
      sha256PadZeroedN scratch q =
        List.replicate (8 * q) (0 : BitVec 8) ++ scratch.drop (8 * q) := by
  intro q hq h
  induction q generalizing scratch with
  | zero => simp [sha256PadZeroedN, List.replicate, List.drop]
  | succ q ih =>
    simp only [sha256PadZeroedN]
    rw [ih scratch (by omega) h]
    exact pad_zero_dword_set scratch q (by simp [h]; omega)

/-- Pad-zero block overwrites every byte with `0` regardless of entry scratch. -/
theorem sha256PadZeroed_eq_replicate (scratch : List (BitVec 8)) (h : scratch.length = 64) :
    sha256PadZeroed scratch = List.replicate 64 (0 : BitVec 8) := by
  rw [← sha256PadZeroedN_eight, sha256PadZeroedN_spec scratch 8 (by decide) h]
  simp [h]

/-- Full 8-dword pad-zero block: B+196 → B+228. -/
theorem sha256PadZeroBlock_spec (scratchBase : Word) (scratch : List (BitVec 8))
    (hscratch : scratch.length = 64) :
    cpsTripleWithin 8 (B + 196) (B + 228) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroed scratch)) := by
  have s0 := pad_step_at scratchBase scratch 0 hscratch (by decide)
  have h1 := pad_zeroedN_len scratch hscratch 1
  have s1 := pad_step_at scratchBase (sha256PadZeroedN scratch 1) 1 h1 (by decide)
  have h2 := pad_zeroedN_len scratch hscratch 2
  have s2 := pad_step_at scratchBase (sha256PadZeroedN scratch 2) 2 h2 (by decide)
  have h3 := pad_zeroedN_len scratch hscratch 3
  have s3 := pad_step_at scratchBase (sha256PadZeroedN scratch 3) 3 h3 (by decide)
  have h4 := pad_zeroedN_len scratch hscratch 4
  have s4 := pad_step_at scratchBase (sha256PadZeroedN scratch 4) 4 h4 (by decide)
  have h5 := pad_zeroedN_len scratch hscratch 5
  have s5 := pad_step_at scratchBase (sha256PadZeroedN scratch 5) 5 h5 (by decide)
  have h6 := pad_zeroedN_len scratch hscratch 6
  have s6 := pad_step_at scratchBase (sha256PadZeroedN scratch 6) 6 h6 (by decide)
  have h7 := pad_zeroedN_len scratch hscratch 7
  have s7 := pad_step_at scratchBase (sha256PadZeroedN scratch 7) 7 h7 (by decide)
  -- Normalize posts to sha256PadZeroedN form.
  have s0' : cpsTripleWithin 1 (B + 196) (B + 200) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase scratch)
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 1)) := by
    simpa [sha256PadZeroedN] using s0
  have s1' : cpsTripleWithin 1 (B + 200) (B + 204) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 1))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 2)) := by
    simpa [sha256PadZeroedN] using s1
  have s2' : cpsTripleWithin 1 (B + 204) (B + 208) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 2))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 3)) := by
    simpa [sha256PadZeroedN] using s2
  have s3' : cpsTripleWithin 1 (B + 208) (B + 212) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 3))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 4)) := by
    simpa [sha256PadZeroedN] using s3
  have s4' : cpsTripleWithin 1 (B + 212) (B + 216) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 4))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 5)) := by
    simpa [sha256PadZeroedN] using s4
  have s5' : cpsTripleWithin 1 (B + 216) (B + 220) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 5))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 6)) := by
    simpa [sha256PadZeroedN] using s5
  have s6' : cpsTripleWithin 1 (B + 220) (B + 224) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 6))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 7)) := by
    simpa [sha256PadZeroedN] using s6
  have s7' : cpsTripleWithin 1 (B + 224) (B + 228) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 7))
      ((.x21 ↦ᵣ scratchBase) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (sha256PadZeroedN scratch 8)) := by
    simpa [sha256PadZeroedN] using s7
  have c01 := cpsTripleWithin_seq_same_cr s0' s1'
  have c02 := cpsTripleWithin_seq_same_cr c01 s2'
  have c03 := cpsTripleWithin_seq_same_cr c02 s3'
  have c04 := cpsTripleWithin_seq_same_cr c03 s4'
  have c05 := cpsTripleWithin_seq_same_cr c04 s5'
  have c06 := cpsTripleWithin_seq_same_cr c05 s6'
  have c07 := cpsTripleWithin_seq_same_cr c06 s7'
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) c07
  simpa [sha256PadZeroedN_eight] using hq

/-- After pad-zero: MV x5=scratch, MV x6=inputCursor, MV x7=rem. B+228→B+240.
    MV focuses rd+rs — frame omits both. -/
theorem sha256PadRemSetup_spec
    (scratchBase inputCursor remW v5 v6 v7 : Word)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 3 (B + 228) (B + 240) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** A)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** (.x7 ↦ᵣ remW) ** A) := by
  have h0 := mv_spec_gen_within .x5 .x21 scratchBase v5 (B + 228) (by decide)
  have h0m := cpsTripleWithin_extend_code
    (mem_at 57 (.MV .x5 .x21) (B + 228) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h0
  rw [show (B + 228 : Word) + 4 = B + 232 from by decide] at h0m
  -- frame omits x5 and x21
  have h0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** A)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hA) h0m
  have h0w : cpsTripleWithin 1 (B + 228) (B + 232) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** A)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** A) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) h0F
  have h1 := mv_spec_gen_within .x6 .x9 inputCursor v6 (B + 232) (by decide)
  have h1m := cpsTripleWithin_extend_code
    (mem_at 58 (.MV .x6 .x9) (B + 232) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h1
  rw [show (B + 232 : Word) + 4 = B + 236 from by decide] at h1m
  -- frame omits x6 and x9
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ scratchBase) ** (.x18 ↦ᵣ remW) **
      (.x5 ↦ᵣ scratchBase) ** (.x7 ↦ᵣ v7) ** A)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hA) h1m
  have h1w : cpsTripleWithin 1 (B + 232) (B + 236) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** A)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** (.x7 ↦ᵣ v7) ** A) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) h1F
  have h2 := mv_spec_gen_within .x7 .x18 remW v7 (B + 236) (by decide)
  have h2m := cpsTripleWithin_extend_code
    (mem_at 59 (.MV .x7 .x18) (B + 236) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) h2
  rw [show (B + 236 : Word) + 4 = B + 240 from by decide] at h2m
  -- frame omits x7 and x18
  have h2F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
      (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** A)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hA) h2m
  have h2w : cpsTripleWithin 1 (B + 236) (B + 240) sha256Cr
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** (.x7 ↦ᵣ v7) ** A)
      ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) ** (.x18 ↦ᵣ remW) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** (.x7 ↦ᵣ remW) ** A) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) h2F
  exact cpsTripleWithin_seq_same_cr (cpsTripleWithin_seq_same_cr h0w h1w) h2w

/-- BEQ rem==0 taken: skip copy+JAL to ADD pad-0x80 setup at B+268 (idx 67). -/
theorem sha256PadRemBeq_empty
    (scratchBase inputCursor : Word) (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 1 (B + 240) (B + 268) sha256Cr
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** A)
      ((.x7 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** A) := by
  have hbr := beq_spec_gen_within .x7 .x0 (28 : BitVec 13)
    (0 : Word) (0 : Word) (B + 240)
  have hbrm := cpsBranchWithin_extend_code
    (mem_at 60 (.BEQ .x7 .x0 (28 : BitVec 13)) (B + 240) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hbr
  have hpc : (B + 240 : Word) + signExtend13 (28 : BitVec 13) = B + 268 := by
    decide
  rw [hpc] at hbrm
  have htaken := cpsBranchWithin_takenStripPure2 hbrm
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hQ).2 (by decide))
  have hfr := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
      (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** A)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hA) htaken
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hfr

/-- BEQ rem≠0 fallthrough into copy loop at B+244. -/
theorem sha256PadRemBeq_nempty
    (scratchBase inputCursor remW : Word) (hne : remW ≠ 0)
    (A : Assertion) (hA : A.pcFree) :
    cpsTripleWithin 1 (B + 240) (B + 244) sha256Cr
      ((.x7 ↦ᵣ remW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** A)
      ((.x7 ↦ᵣ remW) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
        (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** A) := by
  have hbr := beq_spec_gen_within .x7 .x0 (28 : BitVec 13)
    remW (0 : Word) (B + 240)
  have hbrm := cpsBranchWithin_extend_code
    (mem_at 60 (.BEQ .x7 .x0 (28 : BitVec 13)) (B + 240) (by decide)
      (by rw [sha256ProgL_len]; decide) (by rfl)) hbr
  have hpc : (B + 240 : Word) + 4 = B + 244 := by decide
  rw [hpc] at hbrm
  have hnt := cpsBranchWithin_ntakenStripPure2 hbrm
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hQ⟩ := hQt
      exact hne ((sepConj_pure_right _).1 hQ).2)
  have hfr := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ scratchBase) ** (.x9 ↦ᵣ inputCursor) **
      (.x5 ↦ᵣ scratchBase) ** (.x6 ↦ᵣ inputCursor) ** A)
    (by
      repeat' first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact hA) hnt
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hfr

end EvmAsm.Codegen.Proofs
