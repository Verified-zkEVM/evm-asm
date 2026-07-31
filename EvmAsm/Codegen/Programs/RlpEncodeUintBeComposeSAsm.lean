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
-- Same selective open as the sibling: the payload copy is the verified core's
-- `copyN`, and `copyN_eq_append` is the window split that ties it to `reubOut`.
open EvmAsm.Rv64.RLP (copyN copyN_eq_append word_ofNat_add_one)

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

/-- Writing the header byte at index 0 leaves everything from index 1 on alone —
    which is what lets the copy loop's destination window be described against
    the *original* buffer. -/
theorem drop_set_zero (oldOut : List Byte) (b : Byte) (k : Nat) (hk : 1 ≤ k) :
    (oldOut.set 0 b).drop k = oldOut.drop k := by
  cases oldOut with
  | nil => simp
  | cons a t =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp

/-- …and the byte it wrote is the whole of the first cell. -/
theorem take_one_set_zero (oldOut : List Byte) (b : Byte) (h : 0 < oldOut.length) :
    (oldOut.set 0 b).take 1 = [b] := by
  cases oldOut with
  | nil => simp at h
  | cons a t => simp

/-- **The header path's single model target.**  `reubOut_single_large` and
    `reubOut_short_form` are the *same* statement on this path, because
    `0x80 + 1 = 0x81`: the machine writes one `0x80 + L` byte and then the
    payload, for every `L` from 1 to 55 that does not take the raw-byte tail.
    Unifying them here is what keeps the composition free of a sub-case on the
    byte value below the point where the dispatch actually branches on it. -/
theorem reubOut_header_form (xs : List Byte)
    (hlo : 1 ≤ (reubStrip xs).length) (hhi : (reubStrip xs).length ≤ 55)
    (hhdr : ∀ b, reubStrip xs = [b] → ¬ b.toNat < 0x80) :
    reubOut xs
      = BitVec.ofNat 8 (0x80 + (reubStrip xs).length) :: reubStrip xs := by
  by_cases h1 : (reubStrip xs).length = 1
  · obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 h1
    rw [reubOut_single_large xs b hb (hhdr b hb), hb]
    rfl
  · exact reubOut_short_form xs (by omega) hhi

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

/-- The same discharge for the header path, where the copy loop has *already*
    returned `x30` to the caller — so five `regIs`s convert and the sixth is
    passed through. -/
private theorem scratch_to_own_x30 (srcPtr outPtr raVal : Word) (xs newOut : List Byte)
    (n : Nat) (a0 v5 v6 v28 v29 v31 : Word) :
    ∀ h, ((((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) **
      ((.x29 : Reg) ↦ᵣ v29) ** regOwn .x30 ** ((.x31 : Reg) ↦ᵣ v31) **
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
          (sepConj_mono (fun _ x => x)
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

/-! ## §6  The header path (`2 ≤ L ≤ 55`, or `L = 1` with the byte `≥ 0x80`)

    The long path: strip loop breaks, dispatch routes to `reubBase+84` by one of
    two routes, the header byte `0x80 + L` is written, the payload is copied, and
    `a0 = L + 1` comes back.  Six chained specs, and the only path that touches
    the output buffer beyond its first byte.

    **This is where `L ≤ 55` is load-bearing** — `reubOut_header_form` needs it,
    because that is the step at which "the byte the machine wrote" has to equal
    "the byte RLP prescribes".  Above 55 RLP switches to `0xb7 + lenlen` and the
    machine's `0x80 + L` byte, though still correctly computed, is no longer an
    RLP header.

    The two dispatch routes differ only in step count (3 versus 6) and in what
    they leave in `x29`/`x30` — both of which the header write and the copy loop
    overwrite.  So the whole tail from `reubBase+84` on is proved once,
    universally quantified over those two registers (`hrest`), and each route
    instantiates it.  The shorter route is padded to the common bound with
    `cpsTripleWithin_mono_nSteps`. -/

set_option maxRecDepth 8000 in
/-- **Whole routine, header path**: `6*n + 7*L + 17` steps (prologue 2, strip
    loop `6n+1`, dispatch 3 or 6, header write 5, copy loop `7L+1`, tail 2). -/
theorem reub_spec_header (srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 : Word)
    (xs oldOut : List Byte) (n : Nat)
    (hn : xs.length = n) (hn64 : n < 2 ^ 64)
    (hd : reubZeros xs 0 n < n)
    (hhi : n - reubZeros xs 0 n ≤ 55)
    (hhdr : ∀ b, reubStrip xs = [b] → 128 ≤ b.toNat)
    (holen : n + 1 ≤ oldOut.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64) (hoover : outPtr.toNat + (n + 1) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n + 1 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (n * 6 + 7 * (n - reubZeros xs 0 n) + 17) reubBase
      (raVal &&& ~~~1) reubCode
      (reubAbiPre srcPtr outPtr raVal xs oldOut n v5 v6 v28 v29 v30 v31)
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
  set d := reubZeros xs 0 n with hdef
  have hdlen : d < xs.length := by omega
  -- ### the model side: one header byte, then the stripped payload
  have hstrip : reubStrip xs = xs.drop d := reubStrip_eq_drop_zeros xs n hn
  have hLlen : (reubStrip xs).length = n - d := reubStrip_length_eq xs n hn
  have hhdr' : ∀ b, reubStrip xs = [b] → ¬ b.toNat < 0x80 := by
    intro b hb
    have := hhdr b hb
    omega
  -- the byte the `L = 1` dispatch route loads is the payload's only byte
  have hbyte : n - d = 1 → 128 ≤ (xs[d]'hdlen).toNat := by
    intro h1
    refine hhdr _ ?_
    rw [hstrip]
    exact drop_eq_singleton xs d hdlen (by omega)
  have hout : reubOut xs = BitVec.ofNat 8 (0x80 + (n - d)) :: reubStrip xs := by
    have h := reubOut_header_form xs (by omega) (by omega) hhdr'
    rwa [hLlen] at h
  have hlen : (reubOut xs).length = (n - d) + 1 := by
    rw [hout, List.length_cons, hLlen]
  -- ### the model tie: the copy loop's output buffer IS the encoding at the front
  have hregion : copyN (oldOut.set 0 (BitVec.ofNat 8 (128 + (n - d)))) xs 1 d (n - d)
      = reubOut xs ++ oldOut.drop (reubOut xs).length := by
    rw [copyN_eq_append _ _ _ _ _ (by rw [List.length_set]; omega) (by omega),
      take_one_set_zero _ _ (by omega), drop_set_zero _ _ _ (by omega),
      hlen, hout, hstrip,
      List.take_of_length_le (by rw [List.length_drop]; omega),
      show 1 + (n - d) = (n - d) + 1 from by omega]
    rfl
  -- ### the machine side
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
  -- [21]-[34]: header write, copy loop, return tail.  Quantified over the two
  -- registers the two dispatch routes disagree about, both of which are dead by
  -- the time the copy loop finishes.
  have hrest : ∀ w29 w30, cpsTripleWithin (7 * (n - d) + 8) (reubBase + 84)
      (raVal &&& ~~~1) reubCode
      (reubHeaderPre srcPtr outPtr raVal xs oldOut n d w29 w30 **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n))
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
    intro w29 w30
    have hHW := reubHeaderWrite srcPtr outPtr raVal xs oldOut n d w29 w30
      (by omega) hoalign (by omega)
      (by
        have h := hovalid 0 (by omega)
        rwa [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega] at h)
    have hHWF := cpsTripleWithin_frameR
      ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) (by pcFree) hHW
    have hCL := reubCopyLoop srcPtr outPtr w30 xs
      (oldOut.set 0 (BitVec.ofNat 8 (128 + (n - d)))) d 1 (n - d)
      hsalign hoalign (by omega) (by rw [List.length_set]; omega)
      (by omega) (by omega) (by omega)
      (fun k hk => by
        have h := hsvalid (d + k) (by omega)
        exact h)
      (fun k hk => by
        have h := hovalid (1 + k) (by omega)
        exact h)
    have hCLF := cpsTripleWithin_frameR
      (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (128 + (n - d))) **
       ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
       ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n))
      (by pcFree) hCL
    have hRT := reubRetTail raVal srcPtr (n - d)
    have hRTF := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 (d + (n - d)))) **
       ((.x29 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 (1 + (n - d)))) **
       regOwn .x30 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcPtr xs **
       bytesRegion outPtr
         (copyN (oldOut.set 0 (BitVec.ofNat 8 (128 + (n - d)))) xs 1 d (n - d)) **
       ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (128 + (n - d))) **
       ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n))
      (by pcFree) hRT
    have h12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
        simp only [reubCopyPre] at hp
        xperm_hyp hp) hHWF hCLF
    have h123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
        xperm_hyp hp) h12 hRTF
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) h123)
    · simp only [reubHeaderPre, reubAmb] at hp ⊢
      xperm_hyp hp
    · unfold reubAbiPost
      rw [← hregion, hlen, word_ofNat_add_one]
      refine scratch_to_own_x30 srcPtr outPtr raVal xs _ n
        (BitVec.ofNat 64 (n - d) + 1)
        (srcPtr + BitVec.ofNat 64 (d + (n - d))) (0 : Word)
        (BitVec.ofNat 64 (128 + (n - d)))
        (outPtr + BitVec.ofNat 64 (1 + (n - d)))
        (BitVec.ofNat 64 (n - d)) h ?_
      xperm_hyp hp
  -- [12]-[17]: the two dispatch routes into the shared tail
  have htail : ∀ w28, cpsTripleWithin (7 * (n - d) + 14) (reubBase + 48)
      (raVal &&& ~~~1) reubCode
      ((((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) ** bytesRegion srcPtr xs **
        ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion outPtr oldOut **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F) **
       ((.x28 : Reg) ↦ᵣ w28))
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
    intro w28
    by_cases h1 : n - d = 1
    · -- single byte at or above `0x80`: [12]-[17], the `BGEU` taken
      have hdisp := reubDispHeaderLarge srcPtr outPtr raVal xs oldOut n d
        w28 v29 v30 v31 hdlen h1 (hbyte h1) hsalign (by omega) (hsvalid d (by omega))
      have hdispF := cpsTripleWithin_frameR
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) (by pcFree) hdisp
      have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
        hdispF (hrest ((xs[d]'hdlen).zeroExtend 64) (128 : Word))
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hchain)
      simp only [reubDispPre, reubAmb, F] at hp ⊢
      xperm_hyp hp
    · -- payload of any other length: [12]-[14], the `BNE` taken, three steps
      have hdisp := reubDispHeaderLong srcPtr outPtr raVal xs oldOut n d
        w28 v29 v30 v31 h1 hn64
      have hdispF := cpsTripleWithin_frameR
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) (by pcFree) hdisp
      have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
        hdispF (hrest v29 v30)
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hchain)
      simp only [reubDispPre, reubAmb, F] at hp ⊢
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

/-! ## §7  The whole-routine triple

    One `cpsTripleWithin` for `rlp_encode_uint_be`, from `reubBase` to
    `ra &&& ~~~1`, covering **every** input in the routine's documented domain.
    Which of §4/§5/§6's paths runs is decided entirely by data the caller has
    already fixed, so this is a case split on the input list, not on the machine.

    The preconditions are the strongest of the three paths', and each path is
    handed the weaker form it actually needs.  `n ≤ 55` is the ABI's documented
    bound (`RlpRead.lean`); it reaches §6 as `L ≤ 55` via `L ≤ n`, and that is
    the only place it does any work. -/

set_option maxRecDepth 8000 in
/-- **`rlp_encode_uint_be` computes RLP.**  On any `n ≤ 55`-byte big-endian input
    with `n + 1` bytes of output capacity, the routine returns
    `a0 = (reubOut xs).length` and leaves `reubOut xs` at the front of the output
    buffer with the rest of the buffer untouched, in at most
    `6*n + 7*L + 17` steps.

    Three paths are covered and each fires on its own inputs: all-zero
    (`L = 0`, §4), a single byte below `0x80` (§5), and the header path
    (`L = 1` with the byte at or above `0x80`, or `2 ≤ L ≤ 55`, §6). -/
theorem reub_spec_within (srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 : Word)
    (xs oldOut : List Byte) (n : Nat)
    (hn : xs.length = n) (hdom : n ≤ 55)
    (holen : n + 1 ≤ oldOut.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64) (hoover : outPtr.toNat + (n + 1) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n + 1 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (n * 6 + 7 * (n - reubZeros xs 0 n) + 17) reubBase
      (raVal &&& ~~~1) reubCode
      (reubAbiPre srcPtr outPtr raVal xs oldOut n v5 v6 v28 v29 v30 v31)
      (reubAbiPost srcPtr outPtr raVal xs oldOut n) := by
  have hzle : reubZeros xs 0 n ≤ n := reubZeros_le xs 0 n
  have hovalid0 : isValidByteAccess outPtr = true := by
    have h := hovalid 0 (by omega)
    rwa [show outPtr + BitVec.ofNat 64 0 = outPtr from by bv_omega] at h
  by_cases hz : reubZeros xs 0 n = n
  · -- §4: the strip loop exhausted its window
    rw [hz]
    exact cpsTripleWithin_mono_nSteps (by omega)
      (reub_spec_all_zero srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 xs oldOut n
        hn (by omega) hz (by omega) hsalign hoalign hsover (by omega) hsvalid hovalid0)
  · have hd : reubZeros xs 0 n < n := by omega
    have hdlen : reubZeros xs 0 n < xs.length := by omega
    -- a one-byte payload is the byte the loop stopped on
    have hstrip : reubStrip xs = xs.drop (reubZeros xs 0 n) :=
      reubStrip_eq_drop_zeros xs n hn
    have hLlen : (reubStrip xs).length = n - reubZeros xs 0 n :=
      reubStrip_length_eq xs n hn
    have hbeq : ∀ b, reubStrip xs = [b] →
        n - reubZeros xs 0 n = 1 ∧ (xs[reubZeros xs 0 n]'hdlen) = b := by
      intro b hb
      have h1 : n - reubZeros xs 0 n = 1 := by rw [← hLlen, hb]; rfl
      refine ⟨h1, ?_⟩
      have hxb := drop_eq_singleton xs (reubZeros xs 0 n) hdlen (by omega)
      have heq : xs.drop (reubZeros xs 0 n) = [b] := by rw [← hstrip]; exact hb
      rw [hxb] at heq
      simpa using heq
    by_cases h1 : n - reubZeros xs 0 n = 1
    · by_cases hsm : (xs[reubZeros xs 0 n]'hdlen).toNat < 128
      · -- §5: one byte, below `0x80`, stored raw
        exact cpsTripleWithin_mono_nSteps (by omega)
          (reub_spec_single_small srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 xs oldOut n
            hn (by omega) hd h1 hdlen hsm (by omega) hsalign hoalign hsover (by omega)
            hsvalid hovalid0)
      · -- §6: one byte, at or above `0x80`, so the `0x81` header is written
        exact reub_spec_header srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 xs oldOut n
          hn (by omega) hd (by omega)
          (fun b hb => by obtain ⟨_, hbe⟩ := hbeq b hb; rw [← hbe]; omega)
          holen hsalign hoalign hsover hoover hsvalid hovalid
    · -- §6: any other payload length, `0x80 + L` header then the payload
      exact reub_spec_header srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 xs oldOut n
        hn (by omega) hd (by omega)
        (fun b hb => by obtain ⟨h1', _⟩ := hbeq b hb; omega)
        holen hsalign hoalign hsover hoover hsvalid hovalid

/-- **The same claim in scalar form** — the statement an auditor wants, with the
    routine's own `reubOut` eliminated in favour of the reference encoding.  The
    routine writes `rlp.encode(Uint(v))` for the scalar `v` its input denotes, in
    canonical minimal big-endian form: not merely *some* encoding of *some* byte
    string, but the one `execution-specs` prescribes. -/
theorem reub_spec_encode_within (srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 : Word)
    (xs oldOut : List Byte) (n : Nat)
    (hn : xs.length = n) (hdom : n ≤ 55)
    (holen : n + 1 ≤ oldOut.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64) (hoover : outPtr.toNat + (n + 1) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hovalid : ∀ k, k < n + 1 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (n * 6 + 7 * (n - reubZeros xs 0 n) + 17) reubBase
      (raVal &&& ~~~1) reubCode
      (reubAbiPre srcPtr outPtr raVal xs oldOut n v5 v6 v28 v29 v30 v31)
      (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64
          (encodeBytes (Nat.toBytesBE (Nat.fromBytesBE xs))).length) **
       ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       bytesRegion srcPtr xs ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr (encodeBytes (Nat.toBytesBE (Nat.fromBytesBE xs)) ++
         oldOut.drop (encodeBytes (Nat.toBytesBE (Nat.fromBytesBE xs))).length)) := by
  have h := reub_spec_within srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 xs oldOut n
    hn hdom holen hsalign hoalign hsover hoover hsvalid hovalid
  unfold reubAbiPost at h
  rwa [reubOut_eq_encode_toBytesBE] at h

/-! ## §8  Path coverage

    A composition that silently covers only one path is exactly the failure mode
    #10942 was about, so each of the three is exercised at concrete data.  The
    `#guard`s pin *which* path each input takes (`reubZeros` fixes the payload
    length, `reubOut` fixes the encoding), and the `example`s instantiate the
    composed triple at those inputs with the step bound reduced to a literal —
    which it can only do if that path's chain actually fired. -/

-- §4 · all zeros: `L = 0`, output `0x80`, bound `2*6 + 7*0 + 17 = 29`
#guard reubZeros [0, 0] 0 2 = 2
#guard reubOut [0, 0] = [0x80]
-- §5 · one byte below `0x80`: stored raw, bound `2*6 + 7*1 + 17 = 36`
#guard reubZeros [0, 0x2a] 0 2 = 1
#guard reubOut [0, 0x2a] = [0x2a]
-- §6 · one byte at or above `0x80`: `0x81` header, same bound as §5
#guard reubZeros [0, 0x81] 0 2 = 1
#guard reubOut [0, 0x81] = [0x81, 0x81]
-- §6 · two bytes: short-form `0x82` header, bound `2*6 + 7*2 + 17 = 43`
#guard reubZeros [0x01, 0x02] 0 2 = 0
#guard reubOut [0x01, 0x02] = [0x82, 0x01, 0x02]

section PathCoverage

variable {srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 : Word} {oldOut : List Byte}
  (holen : 3 ≤ oldOut.length)
  (hsalign : srcPtr.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
  (hsover : srcPtr.toNat + 2 < 2 ^ 64) (hoover : outPtr.toNat + 3 ≤ 2 ^ 64)
  (hsvalid : ∀ k, k < 2 → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
  (hovalid : ∀ k, k < 3 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true)

/-- §4 fires: all-zero input, 29 steps. -/
example : cpsTripleWithin 29 reubBase (raVal &&& ~~~1) reubCode
    (reubAbiPre srcPtr outPtr raVal [0, 0] oldOut 2 v5 v6 v28 v29 v30 v31)
    (reubAbiPost srcPtr outPtr raVal [0, 0] oldOut 2) :=
  reub_spec_within srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 [0, 0] oldOut 2
    (by decide) (by decide) holen hsalign hoalign hsover hoover hsvalid hovalid

/-- §5 fires: one byte below `0x80`, 36 steps. -/
example : cpsTripleWithin 36 reubBase (raVal &&& ~~~1) reubCode
    (reubAbiPre srcPtr outPtr raVal [0, 0x2a] oldOut 2 v5 v6 v28 v29 v30 v31)
    (reubAbiPost srcPtr outPtr raVal [0, 0x2a] oldOut 2) :=
  reub_spec_within srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 [0, 0x2a] oldOut 2
    (by decide) (by decide) holen hsalign hoalign hsover hoover hsvalid hovalid

/-- §6 fires at `L = 1`: one byte at or above `0x80`, 36 steps. -/
example : cpsTripleWithin 36 reubBase (raVal &&& ~~~1) reubCode
    (reubAbiPre srcPtr outPtr raVal [0, 0x81] oldOut 2 v5 v6 v28 v29 v30 v31)
    (reubAbiPost srcPtr outPtr raVal [0, 0x81] oldOut 2) :=
  reub_spec_within srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 [0, 0x81] oldOut 2
    (by decide) (by decide) holen hsalign hoalign hsover hoover hsvalid hovalid

/-- §6 fires at `L = 2`: the short-form header path, 43 steps. -/
example : cpsTripleWithin 43 reubBase (raVal &&& ~~~1) reubCode
    (reubAbiPre srcPtr outPtr raVal [0x01, 0x02] oldOut 2 v5 v6 v28 v29 v30 v31)
    (reubAbiPost srcPtr outPtr raVal [0x01, 0x02] oldOut 2) :=
  reub_spec_within srcPtr outPtr raVal v5 v6 v28 v29 v30 v31 [0x01, 0x02] oldOut 2
    (by decide) (by decide) holen hsalign hoalign hsover hoover hsvalid hovalid

end PathCoverage

end RlpEncodeUintBeSAsm

end EvmAsm.Codegen
