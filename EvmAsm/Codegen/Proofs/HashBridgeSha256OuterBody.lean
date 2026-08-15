/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256OuterBody

  Outer full-block loop: pure absorb state + focused/unfocused body steps.
  `sha256OuterBody_step` discharges the body hyp of
  `sha256FullBlockLoop_reload_spec` (window-focus + OuterInv reshape).

  CSRS remains an explicit semantic residual (`hsem`) matching Block.lean:
  Accel discharge (params layout → real `sha256Compress`) is a later pure
  bridge, not required to close the countdown shell.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Outer
import EvmAsm.Codegen.Proofs.HashBridgeSha256Block
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.RwSubwindow
import EvmAsm.Rv64.SAsm.PhaseSplit
import EvmAsm.Rv64.ZiskAccel
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Rv64.Accel
set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL
private abbrev sha256BlockStep : Nat := 64
private abbrev sha256OuterBodyFuel : Nat := 22
private abbrev ShaParams : Word := BitVec.ofNat 64 GuestAddrs.sha256_w_params

/-- One SHA-256 compression step on separate 32-byte state + 64-byte block
    buffers, matching the Accel CSRS write-back image. -/
def sha256CompressBytes (st blk : List (BitVec 8)) : List (BitVec 8) :=
  let stD := (List.range 4).map fun i =>
    packBytes (st.drop (8 * i) |>.take 8)
  let blkD := (List.range 8).map fun i =>
    packBytes (blk.drop (8 * i) |>.take 8)
  (u32sToDwords (sha256Compress (dwordsToU32s stD) (dwordsToU32sBE blkD))).flatMap
    dwordBytes

/-- Dword payload the Accel CSRS would write for separate st/blk buffers. -/
def sha256CompressPayload (st blk : List (BitVec 8)) : List Word :=
  let stD := (List.range 4).map fun i =>
    packBytes (st.drop (8 * i) |>.take 8)
  let blkD := (List.range 8).map fun i =>
    packBytes (blk.drop (8 * i) |>.take 8)
  u32sToDwords (sha256Compress (dwordsToU32s stD) (dwordsToU32sBE blkD))

theorem sha256CompressPayload_length (st blk : List (BitVec 8)) :
    (sha256CompressPayload st blk).length = 4 := by
  simp only [sha256CompressPayload]
  have hstD : ((List.range 4).map fun i =>
      packBytes (st.drop (8 * i) |>.take 8)).length = 4 := by
    simp [List.length_map, List.length_range]
  have hu32s : (dwordsToU32s ((List.range 4).map fun i =>
      packBytes (st.drop (8 * i) |>.take 8))).length = 8 := by
    rw [length_dwordsToU32s, hstD]
  rw [length_u32sToDwords, sha256Compress_length _ _ (by omega)]

theorem sha256CompressBytes_eq_payload (st blk : List (BitVec 8)) :
    sha256CompressBytes st blk =
      (sha256CompressPayload st blk).flatMap dwordBytes := rfl

theorem length_sha256CompressBytes (st blk : List (BitVec 8)) :
    (sha256CompressBytes st blk).length = 32 := by
  rw [sha256CompressBytes_eq_payload, length_flatMap_dwordBytes,
    sha256CompressPayload_length]

/-- Operational absorb of the first `k` full 64-byte blocks of `input`,
    starting from IV bytes `st0`. -/
def sha256AbsorbedState (st0 : List (BitVec 8)) (input : List (BitVec 8)) :
    Nat → List (BitVec 8)
  | 0 => st0
  | n + 1 =>
    let st := sha256AbsorbedState st0 input n
    let blk := (input.drop (sha256BlockStep * n)).take sha256BlockStep
    sha256CompressBytes st blk

theorem sha256AbsorbedState_zero (st0 : List (BitVec 8)) (input : List (BitVec 8)) :
    sha256AbsorbedState st0 input 0 = st0 := rfl

theorem sha256AbsorbedState_succ (st0 : List (BitVec 8)) (input : List (BitVec 8))
    (n : Nat) :
    sha256AbsorbedState st0 input (n + 1) =
      sha256CompressBytes (sha256AbsorbedState st0 input n)
        ((input.drop (sha256BlockStep * n)).take sha256BlockStep) := rfl

theorem length_sha256AbsorbedState (st0 : List (BitVec 8)) (input : List (BitVec 8))
    (hst0 : st0.length = 32) (k : Nat) :
    (sha256AbsorbedState st0 input k).length = 32 := by
  induction k with
  | zero => simpa [sha256AbsorbedState] using hst0
  | succ k ih =>
    simp only [sha256AbsorbedState_succ]
    exact length_sha256CompressBytes _ _

/-- Remaining bytes after one body: `64*(n+1)+rem - 64 = 64*n+rem`. -/
theorem sha256_remaining_step (n rem : Nat) :
    sha256BlockStep * (n + 1) + rem - sha256BlockStep = sha256BlockStep * n + rem := by
  simp only [sha256BlockStep]
  omega

/-- Cursor after `done` full blocks. -/
def sha256AbsorbCursor (inputBase : Word) (done : Nat) : Word :=
  inputBase + BitVec.ofNat 64 (sha256BlockStep * done)

theorem sha256AbsorbCursor_zero (inputBase : Word) :
    sha256AbsorbCursor inputBase 0 = inputBase := by
  simp only [sha256AbsorbCursor, sha256BlockStep]
  change inputBase + (0 : Word) = inputBase
  exact BitVec.add_zero inputBase

/-- Cursor advance by one block under a wrap-free bound. -/
theorem sha256AbsorbCursor_succ (inputBase : Word) (done : Nat)
    (hbound : inputBase.toNat + sha256BlockStep * (done + 1) < 2 ^ 64) :
    sha256AbsorbCursor inputBase done + BitVec.ofNat 64 sha256BlockStep =
      sha256AbsorbCursor inputBase (done + 1) := by
  simp only [sha256AbsorbCursor, sha256BlockStep] at hbound ⊢
  apply BitVec.eq_of_toNat_eq
  have hmul : 64 * (done + 1) = 64 * done + 64 := by omega
  rw [hmul] at hbound
  have hdone : 64 * done < 2 ^ 64 := by omega
  have h64 : (64 : Nat) < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hdone, Nat.mod_eq_of_lt h64]
  rw [Nat.mod_eq_of_lt (by omega : 64 * (done + 1) < 2 ^ 64)]
  have hmid : inputBase.toNat + 64 * done < 2 ^ 64 := by omega
  have hsum : inputBase.toNat + 64 * done + 64 < 2 ^ 64 := hbound
  rw [Nat.mod_eq_of_lt hmid, Nat.mod_eq_of_lt hsum]
  change _ = (_ + (64 * done + 64)) % 2 ^ 64
  exact (Nat.mod_eq_of_lt hsum).symm

/-- Block fit: the `done`-th 64-byte window lies inside a message of
    length `64*N+rem`.  Here `n` is remaining full blocks after the step. -/
theorem sha256_blk_fit (N n rem : Nat) (hn : n < N)
    (hfit : sha256BlockStep * N + rem ≤ len) :
    sha256BlockStep * (N - (n + 1)) + sha256BlockStep ≤ len := by
  simp only [sha256BlockStep] at *
  have : 64 * (N - (n + 1)) + 64 = 64 * (N - n) := by omega
  have : 64 * (N - n) ≤ 64 * N := Nat.mul_le_mul_left _ (by omega)
  omega

theorem sha256_blk_length (input : List (BitVec 8)) (N n rem : Nat)
    (hn : n < N) (hfit : sha256BlockStep * N + rem ≤ input.length) :
    ((input.drop (sha256BlockStep * (N - (n + 1)))).take sha256BlockStep).length =
      sha256BlockStep := by
  have hfit' := sha256_blk_fit N n rem hn hfit
  have hdrop :
      (input.drop (sha256BlockStep * (N - (n + 1)))).length ≥ sha256BlockStep := by
    simp only [List.length_drop]
    omega
  rw [List.length_take_of_le hdrop]

/-- `N - (n+1) + 1 = N - n` when `n < N`. -/
theorem sha256_absorbed_done_succ (N n : Nat) (hn : n < N) :
    N - (n + 1) + 1 = N - n := by omega

/-- `ofNat n + (-64) = ofNat (n - 64)` under domain bounds (keccak sub136 pattern). -/
private theorem sub64 (n : Nat) (_hn : 64 ≤ n) (_hb : n < 2 ^ 64) :
    BitVec.ofNat 64 n + (-64 : Word) = BitVec.ofNat 64 (n - 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-64 : Word)).toNat = 18446744073709551552 from by decide]
  omega

/-- Word remaining after ADDI -64 under the signed countdown domain. -/
theorem sha256_remW_step (n rem : Nat)
    (hbound : sha256BlockStep * (n + 1) + rem < 2 ^ 63) :
    BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem) + (-64 : Word) =
      BitVec.ofNat 64 (sha256BlockStep * n + rem) := by
  simp only [sha256BlockStep] at hbound ⊢
  have hle : 64 ≤ 64 * (n + 1) + rem := by omega
  have hb : 64 * (n + 1) + rem < 2 ^ 64 := by omega
  have h := sub64 (64 * (n + 1) + rem) hle hb
  have harith : 64 * (n + 1) + rem - 64 = 64 * n + rem := by omega
  rwa [harith] at h

/-- Outer-loop ambient (fixed bases). Scratch is not pinned (body clobbers).
    x10 is framed outside `OuterInv` (body writes ShaParams; entry is regOwn). -/
def sha256OuterAmb
    (inputBase stateBase scratchBase paramsBase : Word)
    (input params : List (BitVec 8)) : Assertion :=
  (.x8 ↦ᵣ stateBase) ** (.x21 ↦ᵣ scratchBase) **
    bytesRegion inputBase input ** bytesRegion paramsBase params

/-- Invariant with `n` full blocks still remaining.
    `done = N - n` blocks already absorbed; cursor at `inputBase + 64*(N-n)`.
    Deliberately excludes x5/x18 — those are framed by
    `sha256FullBlockLoop_reload_spec` outside `inv`. -/
def sha256OuterInv
    (inputBase stateBase scratchBase paramsBase : Word)
    (input params : List (BitVec 8)) (st0 : List (BitVec 8))
    (N n : Nat) : Assertion :=
  (.x9 ↦ᵣ sha256AbsorbCursor inputBase (N - n)) **
    bytesRegion stateBase (sha256AbsorbedState st0 input (N - n)) **
    sha256OuterAmb inputBase stateBase scratchBase paramsBase input params

theorem sha256OuterAmb_pcFree
    (inputBase stateBase scratchBase paramsBase : Word)
    (input params : List (BitVec 8)) :
    (sha256OuterAmb inputBase stateBase scratchBase paramsBase input params).pcFree := by
  simp only [sha256OuterAmb]
  repeat' first
    | apply pcFree_sepConj
    | exact pcFree_regIs
    | exact bytesRegion_pcFree _ _

theorem sha256OuterInv_pcFree
    (inputBase stateBase scratchBase paramsBase : Word)
    (input params : List (BitVec 8)) (st0 : List (BitVec 8))
    (N n : Nat) :
    (sha256OuterInv inputBase stateBase scratchBase paramsBase
      input params st0 N n).pcFree := by
  simp only [sha256OuterInv]
  exact pcFree_sepConj (by exact pcFree_regIs) <|
    pcFree_sepConj (by exact bytesRegion_pcFree _ _)
      (sha256OuterAmb_pcFree _ _ _ _ _ _)

/-- 64-aligned offset. -/
theorem sha256_offset_mod8 (k : Nat) :
    (sha256BlockStep * k) % 8 = 0 := by
  simp only [sha256BlockStep]; omega

/-- Merge focused window back to full region. -/
theorem bytesRegion_window_unfocus (base : Word) (ws : List (BitVec 8)) (j n : Nat)
    (hfit : j + n ≤ ws.length) (h8j : j % 8 = 0) (h8n : n % 8 = 0) :
    (bytesRegion (base + BitVec.ofNat 64 j) ((ws.drop j).take n) **
        windowRest base ws j n) =
      bytesRegion base ws := by
  exact (bytesRegion_window_focus base ws j n hfit h8j h8n).symm

/-- Focused body step: input already a 64-byte block at `inputCur`.
    Thin wrapper of `sha256FullBlockBody_spec` with payload =
    `sha256CompressPayload st0 blk` (post image = Accel write-back dwords).
    Use `sha256CompressBytes_eq_payload` to rewrite to CompressBytes. -/
theorem sha256OuterBody_step_focused
    (inputCur remW stateBase scratchBase paramsBase : Word)
    (st0 blk scratch params : List (BitVec 8))
    (payload : List Word)
    (v5 v10 : Word)
    (hst : st0.length = 32) (hblk : blk.length = 64)
    (hscratch : scratch.length = 64) (hparams : params.length = 16)
    (hpayload : payload.length = 4)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase st0 ** bytesRegion scratchBase blk) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
      ((.x9 ↦ᵣ inputCur) ** (.x18 ↦ᵣ remW) ** (.x21 ↦ᵣ scratchBase) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x5 ↦ᵣ v5) **
        bytesRegion inputCur blk ** bytesRegion scratchBase scratch **
        bytesRegion stateBase st0 ** bytesRegion paramsBase params)
      ((.x9 ↦ᵣ (inputCur + (64 : Word))) **
        (.x18 ↦ᵣ (remW + (-64 : Word))) **
        (.x21 ↦ᵣ scratchBase) ** (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        regOwn .x5 **
        bytesRegion inputCur blk ** bytesRegion scratchBase blk **
        bytesRegion stateBase (setBytes st0 0 (payload.flatMap dwordBytes)) **
        bytesRegion paramsBase params) :=
  sha256FullBlockBody_spec inputCur remW stateBase scratchBase
    paramsBase blk scratch st0 params payload v5 v10
    hblk hscratch hst hparams hpayload hsem

/-- Focused body with countdown remaining word normalized via `sha256_remW_step`.
    Post x18 is `ofNat (64*n+rem)` rather than `ofNat remaining + (-64)`. -/
theorem sha256OuterBody_step_focused_rem
    (inputCur stateBase scratchBase paramsBase : Word)
    (st0 blk scratch params : List (BitVec 8))
    (payload : List Word)
    (n rem : Nat) (v5 v10 : Word)
    (hst : st0.length = 32) (hblk : blk.length = 64)
    (hscratch : scratch.length = 64) (hparams : params.length = 16)
    (hpayload : payload.length = 4)
    (hbound : sha256BlockStep * (n + 1) + rem < 2 ^ 63)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase st0 ** bytesRegion scratchBase blk) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload)) :
    cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
      ((.x9 ↦ᵣ inputCur) **
        (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
        (.x21 ↦ᵣ scratchBase) **
        (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) ** (.x5 ↦ᵣ v5) **
        bytesRegion inputCur blk ** bytesRegion scratchBase scratch **
        bytesRegion stateBase st0 ** bytesRegion paramsBase params)
      ((.x9 ↦ᵣ (inputCur + (64 : Word))) **
        (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
        (.x21 ↦ᵣ scratchBase) ** (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        regOwn .x5 **
        bytesRegion inputCur blk ** bytesRegion scratchBase blk **
        bytesRegion stateBase (setBytes st0 0 (payload.flatMap dwordBytes)) **
        bytesRegion paramsBase params) := by
  have hremW := sha256_remW_step n rem hbound
  have h := sha256OuterBody_step_focused inputCur
    (BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem))
    stateBase scratchBase paramsBase st0 blk scratch params payload v5 v10
    hst hblk hscratch hparams hpayload hsem
  -- Post of h has x18 = ofNat remaining + (-64); rewrite via hremW.
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) h
  -- hq : post_with_(-64) holds; goal wants post_with ofNat (step*n+rem)
  have hq' := hq
  rw [hremW] at hq'
  exact hq'

/-- `setBytes bs 0 ns = ns` when lengths match (full overwrite). -/
private theorem setBytes_whole (bs ns : List (BitVec 8))
    (hlen : ns.length = bs.length) : setBytes bs 0 ns = ns := by
  refine List.ext_getElem (by rw [length_setBytes, hlen]) ?_
  intro k hk1 hk2
  have hg := getByteAt_setBytes ns bs 0 k (by omega)
  rw [if_pos ⟨by omega, by omega⟩] at hg
  have hgl : getByteAt (setBytes bs 0 ns) k =
      (setBytes bs 0 ns)[k]'hk1 := by
    unfold getByteAt; rw [dif_pos]
  have hgr : getByteAt ns k = ns[k]'hk2 := by
    unfold getByteAt; rw [dif_pos]
  rw [← hgl, hg, Nat.sub_zero, hgr]

/-- Unfocused outer-body step: full `input` region + `OuterInv` + scratch + x10.
    Discharges the body hyp of `sha256FullBlockLoop_reload_spec` after framing
    scratch/x10 (or lifting x10 via `of_forall_regIs_to_regOwn`). -/
theorem sha256OuterBody_step
    (inputBase stateBase scratchBase paramsBase : Word)
    (input params st0 scratch : List (BitVec 8))
    (N rem n : Nat) (v10 : Word)
    (hst0 : st0.length = 32) (hscratch : scratch.length = 64)
    (hparams : params.length = 16)
    (hn : n < N) (_hrem : rem < sha256BlockStep)
    (hfit : sha256BlockStep * N + rem ≤ input.length)
    (hNbound : sha256BlockStep * N + rem < 2 ^ 63)
    (hcur_bound : inputBase.toNat + sha256BlockStep * (N - n) < 2 ^ 64)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      let st := sha256AbsorbedState st0 input (N - (n + 1))
      let blk := (input.drop (sha256BlockStep * (N - (n + 1)))).take sha256BlockStep
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase st ** bytesRegion scratchBase blk) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, sha256CompressPayload st blk)) :
    let blk := (input.drop (sha256BlockStep * (N - (n + 1)))).take sha256BlockStep
    cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
      ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase stateBase scratchBase paramsBase
          input params st0 N (n + 1) **
        (.x10 ↦ᵣ v10) ** bytesRegion scratchBase scratch)
      ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
        (regOwn .x5) **
        sha256OuterInv inputBase stateBase scratchBase paramsBase
          input params st0 N n **
        (.x10 ↦ᵣ ShaParams) ** bytesRegion scratchBase blk) := by
  intro blk
  set st := sha256AbsorbedState st0 input (N - (n + 1))
  have hfit_blk := sha256_blk_fit N n rem hn hfit
  have hblk_len := sha256_blk_length input N n rem hn hfit
  have hj8 := sha256_offset_mod8 (N - (n + 1))
  have hstep8 : sha256BlockStep % 8 = 0 := by simp only [sha256BlockStep]
  have hk_abs := sha256_absorbed_done_succ N n hn
  set j := sha256BlockStep * (N - (n + 1))
  set inputCur := sha256AbsorbCursor inputBase (N - (n + 1))
  have hst_len : st.length = 32 := length_sha256AbsorbedState st0 input hst0 _
  have hbound_step : sha256BlockStep * (n + 1) + rem < 2 ^ 63 := by
    simp only [sha256BlockStep] at hNbound ⊢
    have : 64 * (n + 1) + rem ≤ 64 * N + rem :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    omega
  have hwin := bytesRegion_window_focus inputBase input j sha256BlockStep
    (by simpa [j] using hfit_blk) hj8 hstep8
  have hunf := bytesRegion_window_unfocus inputBase input j sha256BlockStep
    (by simpa [j] using hfit_blk) hj8 hstep8
  set payload := sha256CompressPayload st blk
  have hpayload_len : payload.length = 4 := sha256CompressPayload_length _ _
  have hsem' : ∀ (R : Assertion) (s : MachineState),
      (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
        (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
        bytesRegion stateBase st ** bytesRegion scratchBase blk) ** R).holdsFor s →
      s.csrsValid 0x805 .x10 = true ∧
      s.csrsWrite 0x805 .x10 = (stateBase, payload) := by
    intro R s hp; simpa [payload, st, blk] using hsem R s hp
  have hcur_succ :
      inputCur + BitVec.ofNat 64 sha256BlockStep =
        sha256AbsorbCursor inputBase (N - n) := by
    have hsc := sha256AbsorbCursor_succ inputBase (N - (n + 1)) (by
      simp only [sha256BlockStep] at hcur_bound ⊢
      simpa [hk_abs] using hcur_bound)
    simpa [inputCur, hk_abs] using hsc
  have hst_succ :
      sha256CompressBytes st blk = sha256AbsorbedState st0 input (N - n) := by
    simpa [st, blk, j, hk_abs, sha256BlockStep] using
      (sha256AbsorbedState_succ st0 input (N - (n + 1))).symm
  have hset :
      setBytes st 0 (payload.flatMap dwordBytes) = sha256CompressBytes st blk := by
    have hlen : (payload.flatMap dwordBytes).length = st.length := by
      rw [hst_len, length_flatMap_dwordBytes, hpayload_len]
    rw [setBytes_whole st _ hlen, sha256CompressBytes_eq_payload]
  have hcur_def : inputCur = inputBase + BitVec.ofNat 64 j := rfl
  let Rest : Assertion := windowRest inputBase input j sha256BlockStep
  have hRest : Rest.pcFree := pcFree_windowRest _ _ _ _
  have cF0 := sha256OuterBody_step_focused_rem inputCur stateBase scratchBase
    paramsBase st blk scratch params payload n rem
    (BitVec.ofNat 64 sha256BlockStep) v10
    hst_len (by simpa [blk, j] using hblk_len) hscratch hparams hpayload_len
    hbound_step hsem'
  have cF := cpsTripleWithin_frameR Rest hRest cF0
  refine cpsTripleWithin_weaken
    (fun h hp => by
      -- theorem pre → focused pre ** Rest
      have hp1 :
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
            (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
            (.x9 ↦ᵣ inputCur) ** bytesRegion stateBase st **
            (.x8 ↦ᵣ stateBase) ** (.x21 ↦ᵣ scratchBase) **
            bytesRegion inputBase input ** bytesRegion paramsBase params **
            (.x10 ↦ᵣ v10) ** bytesRegion scratchBase scratch) h := by
        simp only [sha256OuterInv, sha256OuterAmb] at hp
        xperm_hyp hp
      have hp2 :
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
            (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
            (.x9 ↦ᵣ inputCur) ** bytesRegion stateBase st **
            (.x8 ↦ᵣ stateBase) ** (.x21 ↦ᵣ scratchBase) **
            (bytesRegion inputCur blk ** Rest) ** bytesRegion paramsBase params **
            (.x10 ↦ᵣ v10) ** bytesRegion scratchBase scratch) h := by
        simpa [hwin, hcur_def, blk, j, Rest] using hp1
      have hp3 :
          (((.x9 ↦ᵣ inputCur) **
              (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
              (.x21 ↦ᵣ scratchBase) **
              (.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ v10) **
              (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
              bytesRegion inputCur blk ** bytesRegion scratchBase scratch **
              bytesRegion stateBase st ** bytesRegion paramsBase params) **
            Rest) h := by
        xperm_hyp hp2
      exact hp3)
    (fun h hq => by
      -- focused post ** Rest → theorem post
      have hq1 :
          (((.x9 ↦ᵣ (inputCur + (64 : Word))) **
              (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
              (.x21 ↦ᵣ scratchBase) ** (.x8 ↦ᵣ stateBase) **
              (.x10 ↦ᵣ ShaParams) ** regOwn .x5 **
              bytesRegion inputCur blk ** bytesRegion scratchBase blk **
              bytesRegion stateBase (setBytes st 0 (payload.flatMap dwordBytes)) **
              bytesRegion paramsBase params) ** Rest) h := by
        simpa [Rest] using hq
      have hq2 :
          ((.x9 ↦ᵣ (inputCur + (64 : Word))) **
            (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (.x21 ↦ᵣ scratchBase) ** (.x8 ↦ᵣ stateBase) **
            (.x10 ↦ᵣ ShaParams) ** regOwn .x5 **
            bytesRegion inputCur blk ** bytesRegion scratchBase blk **
            bytesRegion stateBase (setBytes st 0 (payload.flatMap dwordBytes)) **
            bytesRegion paramsBase params ** Rest) h := by
        xperm_hyp hq1
      have hq3 :
          ((.x9 ↦ᵣ (inputCur + (64 : Word))) **
            (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (.x21 ↦ᵣ scratchBase) ** (.x8 ↦ᵣ stateBase) **
            (.x10 ↦ᵣ ShaParams) ** regOwn .x5 **
            (bytesRegion inputCur blk ** Rest) **
            bytesRegion scratchBase blk **
            bytesRegion stateBase (setBytes st 0 (payload.flatMap dwordBytes)) **
            bytesRegion paramsBase params) h := by
        xperm_hyp hq2
      have hq4 :
          ((.x9 ↦ᵣ (inputCur + (64 : Word))) **
            (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (.x21 ↦ᵣ scratchBase) ** (.x8 ↦ᵣ stateBase) **
            (.x10 ↦ᵣ ShaParams) ** regOwn .x5 **
            bytesRegion inputBase input **
            bytesRegion scratchBase blk **
            bytesRegion stateBase (setBytes st 0 (payload.flatMap dwordBytes)) **
            bytesRegion paramsBase params) h := by
        have hmerge :
            (bytesRegion inputCur blk ** Rest) = bytesRegion inputBase input := by
          simpa [hcur_def, blk, Rest] using hunf
        simpa [hmerge] using hq3
      have hq5 :
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (regOwn .x5) **
            (.x9 ↦ᵣ sha256AbsorbCursor inputBase (N - n)) **
            bytesRegion stateBase (sha256AbsorbedState st0 input (N - n)) **
            (.x8 ↦ᵣ stateBase) ** (.x21 ↦ᵣ scratchBase) **
            bytesRegion inputBase input ** bytesRegion paramsBase params **
            (.x10 ↦ᵣ ShaParams) ** bytesRegion scratchBase blk) h := by
        have hq4' := hq4
        simp only [hset, hst_succ,
          show inputCur + (64 : Word) =
              inputCur + BitVec.ofNat 64 sha256BlockStep by
            simp only [sha256BlockStep]; rfl,
          hcur_succ] at hq4'
        xperm_hyp hq4'
      simp only [sha256OuterInv, sha256OuterAmb]
      xperm_hyp hq5)
    cF

/-- Outer absorb loop instantiated with `OuterInv` / `sha256AbsorbedState`.
    Scratch is havoc'd (`anyBytes`); x10 is owned (body writes ShaParams). -/
theorem sha256OuterLoop_spec
    (inputBase stateBase scratchBase paramsBase : Word)
    (input params st0 scratch : List (BitVec 8))
    (N rem : Nat) (v10 : Word)
    (hst0 : st0.length = 32) (hscratch : scratch.length = 64)
    (hparams : params.length = 16)
    (hrem : rem < sha256BlockStep)
    (hfit : sha256BlockStep * N + rem ≤ input.length)
    (hNbound : sha256BlockStep * N + rem < 2 ^ 63)
    (hcur : inputBase.toNat + sha256BlockStep * N < 2 ^ 64)
    (hsem : ∀ n, n < N →
      ∀ (R : Assertion) (s : MachineState),
        let st := sha256AbsorbedState st0 input (N - (n + 1))
        let blk := (input.drop (sha256BlockStep * (N - (n + 1)))).take sha256BlockStep
        (((.x8 ↦ᵣ stateBase) ** (.x10 ↦ᵣ ShaParams) **
          (.x21 ↦ᵣ scratchBase) ** bytesRegion paramsBase params **
          bytesRegion stateBase st ** bytesRegion scratchBase blk) ** R).holdsFor s →
        s.csrsValid 0x805 .x10 = true ∧
        s.csrsWrite 0x805 .x10 = (stateBase, sha256CompressPayload st blk)) :
    cpsTripleWithin (N * (22 + 2) + 2) (B + 100) (B + 196) sha256Cr
      ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * N + rem)) **
        (regOwn .x5) **
        sha256OuterInv inputBase stateBase scratchBase paramsBase
          input params st0 N N **
        (.x10 ↦ᵣ v10) ** bytesRegion scratchBase scratch)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
        sha256OuterInv inputBase stateBase scratchBase paramsBase
          input params st0 N 0 **
        (regOwn .x10) ** anyBytes scratchBase 64) := by
  let inv : Nat → Assertion := fun n =>
    sha256OuterInv inputBase stateBase scratchBase paramsBase
      input params st0 N n **
    (regOwn .x10) ** anyBytes scratchBase 64
  have hpcFree : ∀ n, (inv n).pcFree := fun n =>
    pcFree_sepConj (sha256OuterInv_pcFree _ _ _ _ _ _ _ _ _) <|
      pcFree_sepConj (pcFree_regOwn (r := .x10)) (pcFree_anyBytes _ _)
  have hbody : ∀ n, n < N →
      cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
        ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** inv (n + 1))
        ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
          (regOwn .x5) ** inv n) := by
    intro n hn
    have hcur_n : inputBase.toNat + sha256BlockStep * (N - n) < 2 ^ 64 := by
      simp only [sha256BlockStep] at hcur ⊢
      have : N - n ≤ N := Nat.sub_le _ _
      omega
    -- Concrete body: weaken post x10↦ShaParams / bytesRegion → regOwn / anyBytes.
    have c_conc : ∀ (v : Word) (sc : List (BitVec 8)), sc.length = 64 →
        cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
            (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
            sha256OuterInv inputBase stateBase scratchBase paramsBase
              input params st0 N (n + 1) **
            (.x10 ↦ᵣ v) ** bytesRegion scratchBase sc)
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (regOwn .x5) ** inv n) := by
      intro v sc hsc
      have hs := sha256OuterBody_step inputBase stateBase scratchBase paramsBase
        input params st0 sc N rem n v hst0 hsc hparams hn hrem hfit hNbound
        hcur_n (hsem n hn)
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hs
      simp only [inv]
      have hlen := sha256_blk_length input N n rem hn hfit
      have hq' :
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (regOwn .x5) **
            sha256OuterInv inputBase stateBase scratchBase paramsBase
              input params st0 N n **
            (.x10 ↦ᵣ ShaParams) **
            bytesRegion scratchBase
              ((input.drop (sha256BlockStep * (N - (n + 1)))).take
                sha256BlockStep)) h := by
        simpa using hq
      have htrail :
          ∀ h',
            ((.x10 ↦ᵣ ShaParams) **
              bytesRegion scratchBase
                ((input.drop (sha256BlockStep * (N - (n + 1)))).take
                  sha256BlockStep)) h' →
            ((regOwn .x10) ** anyBytes scratchBase 64) h' := by
        intro h' hp
        obtain ⟨ha, hb, hd, hu, hx10, hbytes⟩ := hp
        refine ⟨ha, hb, hd, hu, regIs_to_regOwn .x10 ShaParams ha hx10, ?_⟩
        have hany := bytesRegion_anyBytes scratchBase _ hb hbytes
        simpa [hlen] using hany
      -- `**` is right-assoc: peel x18, x5, OuterInv to reach the trailing pair.
      refine sepConj_mono_right ?_ h hq'
      intro h1 hp1
      refine sepConj_mono_right ?_ h1 hp1
      intro h2 hp2
      exact sepConj_mono_right htrail h2 hp2
    -- Lift anyBytes (must be trailing as `P ** anyBytes`).
    have c_any : ∀ v : Word,
        cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
            (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
            sha256OuterInv inputBase stateBase scratchBase paramsBase
              input params st0 N (n + 1) **
            (.x10 ↦ᵣ v) ** anyBytes scratchBase 64)
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (regOwn .x5) ** inv n) := by
      intro v
      let P : Assertion :=
        (.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
          sha256OuterInv inputBase stateBase scratchBase paramsBase
            input params st0 N (n + 1) **
          (.x10 ↦ᵣ v)
      have hpre := cpsTripleWithin_anyBytes_pre (P := P) (b := scratchBase) (len := 64)
        (fun sc hsc => by
          refine cpsTripleWithin_weaken
            (fun h hp => by xperm_hyp hp)
            (fun _ hq => hq)
            (c_conc v sc hsc))
      refine cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun _ hq => hq)
        hpre
    -- Lift regOwn: put x10 trailing after anyBytes, then of_forall, then xperm back.
    have c_own :
        cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
            (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
            sha256OuterInv inputBase stateBase scratchBase paramsBase
              input params st0 N (n + 1) **
            (regOwn .x10) ** anyBytes scratchBase 64)
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
            (regOwn .x5) ** inv n) := by
      have c_swap : ∀ v,
          cpsTripleWithin 22 (B + 108) (B + 100) sha256Cr
            (((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
                (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) **
                sha256OuterInv inputBase stateBase scratchBase paramsBase
                  input params st0 N (n + 1) **
                anyBytes scratchBase 64) **
              (.x10 ↦ᵣ v))
            ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
              (regOwn .x5) ** inv n) := by
        intro v
        refine cpsTripleWithin_weaken
          (fun h hp => by xperm_hyp hp)
          (fun _ hq => hq)
          (c_any v)
      have c_trail :=
        cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10) c_swap
      refine cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun _ hq => hq)
        c_trail
    simpa only [inv] using c_own
  have hloop := sha256FullBlockLoop_reload_spec N rem inv hpcFree hrem hNbound hbody
  refine cpsTripleWithin_weaken
    (fun h hp => by
      have htrail :
          ∀ h', ((.x10 ↦ᵣ v10) ** bytesRegion scratchBase scratch) h' →
            ((regOwn .x10) ** anyBytes scratchBase 64) h' := by
        intro h' hp'
        obtain ⟨ha, hb, hd, hu, hx10, hbytes⟩ := hp'
        refine ⟨ha, hb, hd, hu, regIs_to_regOwn .x10 v10 ha hx10, ?_⟩
        have hany := bytesRegion_anyBytes scratchBase scratch hb hbytes
        simpa [hscratch] using hany
      have hp1 :
          ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * N + rem)) **
            (regOwn .x5) **
            sha256OuterInv inputBase stateBase scratchBase paramsBase
              input params st0 N N **
            (regOwn .x10) ** anyBytes scratchBase 64) h := by
        refine sepConj_mono_right ?_ h hp
        intro h1 hp1
        refine sepConj_mono_right ?_ h1 hp1
        intro h2 hp2
        exact sepConj_mono_right htrail h2 hp2
      simpa [inv] using hp1)
    (fun h hq => by simpa [inv] using hq)
    hloop

end EvmAsm.Codegen.Proofs
