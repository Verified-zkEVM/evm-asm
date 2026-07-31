/-
  EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm

  **The whole-routine triple for `rlp_encode_uint_be`** — the composition of the
  block theorems in `RlpEncodeUintBeSAsm.lean` into a single
  `cpsTripleWithin … reubBase (ra &&& ~~~1)`, and with it the first statement
  that the routine *computes RLP* rather than that its blocks do twelve things.

  Sibling module because the block file is at 1475 of the hard 1500-line cap
  under `Codegen/Programs`; the precedent for splitting one routine across
  modules is `WithdrawalDecodeClose` → `Close2..5`.

  ## Why this is where `≤ 55` finally matters

  No block theorem needs the domain bound — `truncate_header_byte` is
  deliberately unconditional, and for a stripped payload of 128 bytes or more
  the header byte simply wraps while every block equation still holds.  The
  bound becomes load-bearing exactly here, where the written region is tied to
  `reubOut`: `reubOut_short_form` is the step that requires it, because that is
  the step where "what the machine wrote" has to equal "what RLP says".

  ## The three paths

  All three return to `ra &&& ~~~1`, so the composition is a triple, not a
  branch.  Which one runs is decided by data the caller already fixed, so the
  proof splits on `L = (reubStrip xs).length` *before* touching the machine —
  the same discipline that made each block lemma a straight-line `runBlock`
  chain:

  | `L` | path | model lemma |
  |---|---|---|
  | `0` | strip loop exhausts → `0x80` | `reubOut_of_all_zero` |
  | `1`, byte `< 0x80` | single-byte tail, byte stored raw | `reubOut_single_small` |
  | `1`, byte `≥ 0x80` | header path, `0x81` then the byte | `reubOut_single_large` |
  | `2..55` | header path, `0x80+L` then the payload | `reubOut_short_form` |

  In each case ONE arm of `reubStripLoop` is vacuous by pure-fact
  contradiction: the break post carries `⌜d = reubZeros xs 0 n ∧ d < n⌝` and the
  exhaustion post carries `⌜reubZeros xs 0 n = n⌝`, and those cannot both hold.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.RlpEncodeUintBeSAsm

namespace EvmAsm.Codegen

namespace RlpEncodeUintBeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP

/-! ## §1  The ABI-level pre and post

    Scratch registers are explicit values on the way in (matching every block
    theorem in the sibling module) and `regOwn` on the way out, because each of
    the three paths leaves them holding different things — a single concrete
    post would silently pin one path's register state. -/

/-- The routine's entry state: `a0` the source pointer, `a1` the length, `a2`
    the output pointer, plus the six registers it clobbers. -/
def reubAbiPre (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n : Nat)
    (v5 v6 v28 v29 v30 v31 : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
  ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) **
  ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
  bytesRegion srcPtr xs ** ((.x12 : Reg) ↦ᵣ outPtr) **
  ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion outPtr oldOut

/-- The routine's exit state: `a0` is the number of bytes written, the output
    buffer begins with `reubOut xs` and is otherwise untouched, and the source
    region is unchanged. -/
def reubAbiPost (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n : Nat) :
    Assertion :=
  ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (reubOut xs).length) **
  ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
  regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  bytesRegion srcPtr xs ** ((.x12 : Reg) ↦ᵣ outPtr) **
  ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion outPtr (reubOut xs ++ oldOut.drop (reubOut xs).length)

/-! ## §2  Model bridges the composition needs

    `reubStrip_drop_eq` is stated at an arbitrary offset; at offset zero with
    `xs.length = n` it says the stripped payload is the suffix the loop stopped
    at, which is what every path's output claim is phrased against. -/

/-- The stripped payload is the suffix past the counted leading zeros. -/
theorem reubStrip_eq_drop_zeros (xs : List Byte) (n : Nat) (hn : xs.length = n) :
    reubStrip xs = xs.drop (reubZeros xs 0 n) := by
  have h := reubStrip_drop_eq xs 0 n (by omega)
  rw [List.drop_zero, Nat.zero_add] at h
  exact h

/-- The payload length the machine carries in `x31` is the model's. -/
theorem reubStrip_length_eq (xs : List Byte) (n : Nat) (hn : xs.length = n) :
    (reubStrip xs).length = n - reubZeros xs 0 n := by
  rw [reubStrip_eq_drop_zeros xs n hn, List.length_drop, hn]

/-- Exhaustion means every byte was zero. -/
theorem reubStrip_nil_of_zeros_eq (xs : List Byte) (n : Nat) (hn : xs.length = n)
    (hz : reubZeros xs 0 n = n) : reubStrip xs = [] := by
  rw [reubStrip_eq_drop_zeros xs n hn, hz, ← hn, List.drop_length]

/-- Writing one byte at the front of a nonempty buffer is `[b] ++ tail`. -/
theorem set_zero_eq_append (oldOut : List Byte) (b : Byte) (h : 0 < oldOut.length) :
    oldOut.set 0 b = [b] ++ oldOut.drop 1 := by
  cases oldOut with
  | nil => simp at h
  | cons a t => simp

/-- A one-byte suffix is the singleton of its last element — the `L = 1` case's
    bridge from `reubStrip xs = xs.drop d` to `reubStrip xs = [xs[d]]`. -/
theorem drop_eq_singleton (xs : List Byte) (d : Nat) (hd : d < xs.length)
    (h1 : d + 1 = xs.length) : xs.drop d = [xs[d]'hd] := by
  rw [List.drop_eq_getElem_cons hd, List.drop_eq_nil_of_le (by omega)]

/-! ## §3  The scratch-register discharge, shared by all three paths

    Each path exits with the six clobbered registers holding *different*
    concrete values, so `reubAbiPost` has to own them rather than name them.
    One implication does that for every path. -/

/-- Six concrete scratch values imply the post's six `regOwn`s. -/
private theorem scratch_to_own (srcPtr outPtr raVal : Word) (xs newOut : List Byte)
    (n : Nat) (a0 v5 v6 v28 v29 v30 v31 : Word) :
    ∀ h, ((((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) **
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
      ((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
      bytesRegion srcPtr xs ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr newOut)) h →
    ((((.x10 : Reg) ↦ᵣ a0) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion srcPtr xs ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion outPtr newOut)) h := by
  intro h hp
  have h1 := sepConj_mono (regIs_implies_regOwn .x5)
    (sepConj_mono (regIs_implies_regOwn .x6)
      (sepConj_mono (regIs_implies_regOwn .x28)
        (sepConj_mono (regIs_implies_regOwn .x29)
          (sepConj_mono (regIs_implies_regOwn .x30)
            (sepConj_mono (regIs_implies_regOwn .x31) (fun _ x => x)))))) h hp
  xperm_hyp h1

/-! ## §4  The all-zeros path (`L = 0`)

    The strip loop exhausts its window, so §3's tail writes `0x80` and returns
    `a0 = 1`.  `reubOut_of_all_zero` is the model side. -/

set_option maxRecDepth 8000 in
/-- **Whole routine, all-zeros input**: `reubBase → ra &&& ~~~1` in `n*6 + 7`
    steps (prologue 2, strip loop `n*6+1`, tail 4). -/
theorem reub_spec_all_zero (srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 : Word)
    (xs oldOut : List Byte) (n : Nat)
    (hn : xs.length = n) (hn64 : n < 2 ^ 64)
    (hz : reubZeros xs 0 n = n)
    (holen : 0 < oldOut.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64) (hoover : outPtr.toNat < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin (n * 6 + 7) reubBase (raVal &&& ~~~1) reubCode
      (reubAbiPre srcPtr outPtr raVal xs oldOut n v5 v6 v28 v29 v30 v31)
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
  -- the model side
  have hall : ∀ b ∈ xs, b = 0 :=
    (reubStrip_eq_nil_iff xs).1 (reubStrip_nil_of_zeros_eq xs n hn hz)
  have hout : reubOut xs = [BitVec.ofNat 8 0x80] := reubOut_of_all_zero xs hall
  have hlen1 : (reubOut xs).length = 1 := by rw [hout]; rfl
  -- the frame the prologue and loop carry but do not touch
  let F : Assertion :=
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)
  have hF : F.pcFree := by unfold F; pcFree
  -- [0]-[1]
  have hpro := cpsTripleWithin_frameR F hF
    (reubPrologue srcPtr outPtr raVal v5 v6 v28 xs oldOut n)
  -- [2]-[7], exhaustion arm: the break post is unsatisfiable when every byte is zero
  have hloop0 := reubStripLoop srcPtr outPtr raVal xs oldOut n (by omega) hn64
    hsalign hsover hsvalid
  have hloop := cpsBranchWithin_frameR
    (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F) (by unfold F; pcFree) hloop0
  have hexh := cpsBranchWithin_ntakenPath hloop (fun _ hQt => by
    obtain ⟨_, _, _, _, hBreak, _⟩ := hQt
    obtain ⟨d, hd⟩ := hBreak
    have hpure := ((sepConj_pure_right _).1 hd).2
    omega)
  -- [8]-[11], after naming the scratch byte register.  `x28` must be the
  -- OUTERMOST right factor or `cpsTripleWithin_of_forall_regIs_to_regOwn`
  -- cannot see it — the same nesting constraint the block lemmas hit.
  have htail : ∀ w28, cpsTripleWithin 4 (reubBase + 32) (raVal &&& ~~~1) reubCode
      ((((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) ** bytesRegion srcPtr xs **
        ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion outPtr oldOut **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F) **
       ((.x28 : Reg) ↦ᵣ w28))
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
    intro w28
    have h0 := reubEmptyTail outPtr raVal w28 srcPtr oldOut hoalign holen hoover hovalid
    have h1 := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) ** bytesRegion srcPtr xs **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)
      (by unfold F; pcFree) h0
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) h1
    · unfold F at hp ⊢; xperm_hyp hp
    · unfold reubAbiPost
      rw [hlen1, hout, ← set_zero_eq_append oldOut (BitVec.ofNat 8 0x80) holen]
      refine scratch_to_own srcPtr outPtr raVal xs _ n (1 : Word)
        (srcPtr + BitVec.ofNat 64 n) (BitVec.ofNat 64 (n - n)) (128 : Word)
        v29 v30 v31 h ?_
      unfold F at hp
      xperm_hyp hp
  -- chain: (loop-exhaust ; tail), then prologue in front
  have hmid := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      -- reubExhPost ** frame → (everything) ** regOwn x28; the pure factor is
      -- dropped rather than peeled, since `hz` already gives it in Lean.
      unfold reubExhPost reubInvCore reubStable reubAmb at hp
      unfold F at hp ⊢
      have hp1 := sepConj_mono_left
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp
      xperm_hyp hp1) hexh
    (cpsTripleWithin_of_forall_regIs_to_regOwn (fun w28 => htail w28))
  have hfull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by unfold F at hp ⊢; xperm_hyp hp) hpro hmid
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hfull)
  unfold reubAbiPre at hp
  unfold F
  xperm_hyp hp

/-! ## §5  The single-small-byte path (`L = 1`, byte `< 0x80`)

    The strip loop breaks, the dispatch falls all the way through, and the byte
    is stored raw: `reubOut_single_small` on the machine.  Here the *exhaustion*
    arm is the vacuous one. -/

set_option maxRecDepth 8000 in
/-- **Whole routine, single byte below `0x80`**: `n*6 + 12` steps
    (prologue 2, strip loop `n*6+1`, dispatch 6, tail 3). -/
theorem reub_spec_single_small (srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 : Word)
    (xs oldOut : List Byte) (n : Nat)
    (hn : xs.length = n) (hn64 : n < 2 ^ 64)
    (hd : reubZeros xs 0 n < n)
    (hL : n - reubZeros xs 0 n = 1)
    (hdlen : reubZeros xs 0 n < xs.length)
    (hsmall : (xs[reubZeros xs 0 n]'hdlen).toNat < 128)
    (holen : 0 < oldOut.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64) (hoover : outPtr.toNat < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin (n * 6 + 12) reubBase (raVal &&& ~~~1) reubCode
      (reubAbiPre srcPtr outPtr raVal xs oldOut n v5 v6 v28 v29 v30 v31)
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
  set d := reubZeros xs 0 n with hdef
  set b := xs[d]'hdlen with hbdef
  -- the model side
  have hstrip : reubStrip xs = [b] := by
    rw [reubStrip_eq_drop_zeros xs n hn, ← hdef]
    exact drop_eq_singleton xs d hdlen (by omega)
  have hout : reubOut xs = [b] := reubOut_single_small xs b hstrip (by omega)
  have hlen1 : (reubOut xs).length = 1 := by rw [hout]; rfl
  let F : Assertion :=
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31)
  have hF : F.pcFree := by unfold F; pcFree
  have hpro := cpsTripleWithin_frameR F hF
    (reubPrologue srcPtr outPtr raVal v5 v6 v28 xs oldOut n)
  -- [2]-[7], break arm: exhaustion would need `reubZeros = n`, but `d < n`
  have hloop0 := reubStripLoop srcPtr outPtr raVal xs oldOut n (by omega) hn64
    hsalign hsover hsvalid
  have hloop := cpsBranchWithin_frameR
    (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F) (by unfold F; pcFree) hloop0
  have hbrk := cpsBranchWithin_takenPath hloop (fun _ hQf => by
    obtain ⟨_, _, _, _, hExh, _⟩ := hQf
    unfold reubExhPost at hExh
    have hpure := ((sepConj_pure_right _).1 hExh).2
    omega)
  -- [12]-[20]: dispatch falls through, then the raw-byte tail
  have htail : ∀ w28, cpsTripleWithin 9 (reubBase + 48) (raVal &&& ~~~1) reubCode
      ((((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) ** bytesRegion srcPtr xs **
        ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion outPtr oldOut **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F) **
       ((.x28 : Reg) ↦ᵣ w28))
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
    intro w28
    have hdisp := reubDispSmallSingle srcPtr outPtr raVal xs oldOut n d
      w28 v29 v30 v31 hdlen hL hsmall hsalign (by omega) (hsvalid d (by omega))
    have hsing := reubSingleTail outPtr raVal srcPtr b oldOut hoalign holen hoover hovalid
    -- frame each to the full state, then chain
    have hdispF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n)) (by pcFree) hdisp
    have hsingF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
       ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x30 : Reg) ↦ᵣ (128 : Word)) **
       ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
       bytesRegion srcPtr xs ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n)) (by pcFree) hsing
    have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
        simp only [reubSinglePre, reubAmb] at hp
        xperm_hyp hp) hdispF hsingF
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hchain
    · simp only [reubDispPre, reubAmb, F] at hp ⊢
      xperm_hyp hp
    · unfold reubAbiPost
      rw [hlen1, hout, ← set_zero_eq_append oldOut b holen]
      refine scratch_to_own srcPtr outPtr raVal xs _ n (1 : Word)
        (srcPtr + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n - d)) (1 : Word)
        (b.zeroExtend 64) (128 : Word) (BitVec.ofNat 64 (n - d)) h ?_
      xperm_hyp hp
  -- chain: (loop-break ; dispatch+tail), then prologue in front
  have hmid := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      obtain ⟨h1, h2, hd12, hu, hBreak, hFr⟩ := hp
      obtain ⟨dd, hdd⟩ := hBreak
      obtain ⟨hcore, hpure⟩ := (sepConj_pure_right h1).1 hdd
      obtain ⟨rfl, _⟩ := hpure
      have hp' : (reubInvCore srcPtr outPtr raVal xs oldOut n d **
          (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)) h :=
        ⟨h1, h2, hd12, hu, hcore, hFr⟩
      simp only [reubInvCore, reubStable, reubAmb, F] at hp'
      simp only [F] at ⊢
      xperm_hyp hp') hbrk
    (cpsTripleWithin_of_forall_regIs_to_regOwn (fun w28 => htail w28))
  have hfull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by unfold F at hp ⊢; xperm_hyp hp) hpro hmid
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hfull)
  unfold reubAbiPre at hp
  unfold F
  xperm_hyp hp

end RlpEncodeUintBeSAsm

end EvmAsm.Codegen
