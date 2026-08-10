/-
  EvmAsm.Codegen.Programs.RlpEncodeUintBeSAsm

  `rlp_encode_uint_be` (`rlpEncodeUintBe_prog`, 35 instructions,
  `RlpRead.lean:471`) — the canonical RLP scalar encoder: strip the leading
  zero bytes off a big-endian input buffer and emit the RLP encoding of what
  remains.  Leaf, no stack frame, no callees; `t0`/`t1`/`t3`/`t4`/`t5`/`x31`
  clobbered, everything else preserved, returns to `ra &&& ~~~1`.

  Lives under `Codegen/Programs` (layering L1: the verified core may not import
  `Codegen`) because it pins the linked guest entry
  `GuestAddrs.rlp_encode_uint_be` — same shape as `RlpSpliceHelperSpec.lean`
  and `RlpBytesEncodedSizeSAsm.lean`.

  ## The specification is stated against the pure RLP model, not the assembly

  The post ties the written bytes to `EvmAsm.EL.RLP.encodeBytes` composed with
  a leading-zero strip, and `reubStrip_eq_toBytesBE` then identifies that strip
  with `Nat.toBytesBE ∘ Nat.fromBytesBE` — the minimal big-endian form.  So the
  three canonical-form properties the routine exists to provide

    * zero encodes as the empty string `0x80`,
    * a single byte below `0x80` encodes as itself,
    * the output never carries a leading zero byte,

  are corollaries of the *model*, not separate assertions about the machine.
  Stating them the other way round — via the routine's own byte-picking — would
  be satisfied by an encoder that strips wrongly and checks itself.

  ## Domain: `len ≤ 55`

  `reubOut_short_form` requires the stripped payload to be at most 55 bytes, and
  the eventual machine triple will require `xs.length ≤ 55`.  This is a real
  restriction, not bookkeeping: instructions [21]-[23] write the header as
  `0x80 + n` unconditionally, whereas RLP requires the `0xb7 + lenlen` long form
  once the payload reaches 56 bytes, so the routine is only correct below that
  boundary.

  ### Call sites as of this commit: 21 across 7 files, 20 of which are in domain

  Enumerated rather than sampled, because a future caller is what this note
  exists to protect against.  Regenerate with **both** greps — form 1 alone
  misses three of the seven files:

      grep -rn 'jal ra, rlp_encode_uint_be' EvmAsm/
      grep -rn 'GuestAddrs.rlp_encode_uint_be' EvmAsm/ | grep -v GuestAddrs.lean

  (Form 2 also matches this module and `Proofs/GuestImageEntries.lean`, a layout
  table; neither is a caller.)

  | file | form | sites | `a1` |
  |---|---|---|---|
  | `BlockHeaderSszToRlp` | string | 9 | `li a1, 8` ×8, `li a1, 32` ×1 |
  | `Withdrawal` | string | 3 | `li a1, 8` |
  | `State` (`account_encode`) | string | 2 | `li a1, 8`, `li a1, 32` |
  | `StorageRoot` | string | 1 | `li a1, 32` |
  | `SszWithdrawal` | `.JAL` | 3 | `.LI .x11 8` |
  | `TxSigningHash` | `.JAL` | 1 | `.LI .x11 8` |
  | `AccountBalance` | `.JAL` | 1 | `.MV .x11 .x20`, guarded — see below |

  `AccountBalance`'s site passes a register, not a literal, and is in domain for
  a stronger reason than the others: `account_set_uint_field` guards it two
  instructions before the call (`.LI .x5 32; .BLTU .x5 .x20 → value-too-long
  exit`), so `a1 ≤ 32` holds dynamically, matching that routine's ABI docstring.

  ### The one exception: the probe caller is unbounded

  `zisk_rlp_encode_uint_be` (`ziskRlpEncodeUintBePrologue`, `State.lean`) does
  `ld a1, 8(a3)` with `a3 = 0x40000000` — the source length comes straight from
  host input with no bound check.  So the precondition does **not** discharge
  there, and the probe can drive the routine past 56 bytes, where it emits a
  short header for a long payload.

  Not a consensus-path defect (it is a probe BuildUnit, not production guest
  code), but the probe is **not a sound oracle above 55 bytes**: a mismatch
  against a reference encoder at `src_len ≥ 56` is this domain restriction, not
  a defect in whatever is under test.

  ## Machine coverage — every instruction, in blocks; the composition is a sibling

  All 35 instructions are covered by a block theorem, and the composition over
  them **has since landed** in `RlpEncodeUintBeComposeSAsm.lean` (see "Status" at
  the end of this section).  The blocks:

    * §1, §1b — the pure layer;  §2 — the guest layout
    * §8 — the prologue [0]-[1] (`reubPrologue`), establishing `reubInv … 0`
    * §3 — the all-zeros tail [8]-[11]
    * §4 — the leading-zero strip loop [2]-[7], `reubStripRound` and
      `reubStripExh` folded by `twoExitRetLoop_spec` into one
      `cpsBranchWithin (n * 6 + 1)` reaching *either* `reubBase+48` (a nonzero
      byte, count pinned) *or* `reubBase+32` (all bytes zero)
    * §5 — the single-byte dispatch [12]-[17], split three ways
      (`reubDispHeaderLong`, `reubDispHeaderLarge`, `reubDispSmallSingle`), and
      its tail [18]-[20] (`reubSingleTail`)
    * §6 — the payload copy loop [26]-[32] (`reubCopyLoop`), by induction on the
      counter, posting `copyN` — the verified core's definition, reused
    * §7 — the header write [21]-[25] (`reubHeaderWrite`) and the return tail
      [33]-[34] (`reubRetTail`)

  ### Status: the composition landed in a sibling module

  No whole-routine triple lives in *this file*, deliberately — it is at the hard
  1500-line cap, so the composition went to a sibling as planned (precedent:
  `WithdrawalDecodeClose` → `Close2..5`).

  ⇒ The whole-routine triples are in **`RlpEncodeUintBeComposeSAsm.lean`**:
  `reub_spec_within`, `reub_spec_within_of_length_le`, `reub_spec_encode_within`,
  all three registered in `Progress/Routines.lean` as `.conditional` on `≤ 55`.
  Chaining §8 → §4 → (§3 | §5 | §7) for `reubBase → ra &&& ~~~1` is where
  `reubOut_short_form` and `reubZeros_sub_length` do their work; **no block lemma
  here needs `≤ 55`** (see `truncate_header_byte`, deliberately unconditional).
  Block coverage in this file is therefore not itself the claim that
  `rlp_encode_uint_be` computes RLP — that claim is the sibling's, and it is gated.

  ⚠️ **`.conditional` is the honest ceiling for this routine as emitted, not a
  proof shortfall.**  Instructions [21]-[23] are `LI x28, 128; ADD x28, x28, x31;
  SB x12, x28, 0` — header `0x80 + n` **unconditionally**, with no
  `0xb7 + lenlen` path in the 35 instructions.  No proof upgrades this to
  `.proven`; above 55 bytes it emits a short header for a long payload, which is
  an emitted-code question.  (Contrast `rlp_encode_list_prefix`, which *does*
  implement its long form — lenlen 1..8, header `0xf7 + lenlen` — so there the
  long-form arm is real proof work.)  Recorded because "conditional" invites an
  upgrade attempt that cannot succeed here.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SAsm.MeasureLoop
import EvmAsm.Rv64.RLP.ContentToU256Be
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Evm64.CallingConvention
import EvmAsm.EL.RLP.Properties
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

namespace RlpEncodeUintBeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
-- `copyN` and the counter/pointer word lemmas are the verified core's, not
-- re-derived here: the payload copy loop [26]-[32] is the same seven
-- instructions as `cu256_loop_spec_within`'s, register-renamed.
open EvmAsm.Rv64.RLP (copyN copyN_zero copyN_succ copyN_length
  word_ofNat_succ_dec word_ofNat_succ_ne_zero word_ofNat_add_one)

/-! ## §1  Pure layer: the leading-zero strip and the canonical encoding

    `reubStrip` is the independent definition of what instructions [2]-[7] do;
    `reubOut` is the independent definition of the whole routine's output. -/

/-- Drop leading zero bytes from a big-endian byte list. -/
def reubStrip : List Byte → List Byte
  | [] => []
  | b :: bs => if b = 0 then reubStrip bs else b :: bs

@[simp] theorem reubStrip_nil : reubStrip [] = [] := rfl

theorem reubStrip_cons_zero (bs : List Byte) :
    reubStrip ((0 : Byte) :: bs) = reubStrip bs := by
  simp [reubStrip]

theorem reubStrip_cons_ne (b : Byte) (bs : List Byte) (h : b ≠ 0) :
    reubStrip (b :: bs) = b :: bs := by
  rw [show reubStrip (b :: bs) = if b = 0 then reubStrip bs else b :: bs from rfl,
      if_neg h]

/-- **No leading zero in the stripped list** — the canonicity witness, and the
    hypothesis `Nat.toBytesBE_fromBytesBE_of_canonical` asks for.  `headD 1`
    makes the empty list vacuously canonical, matching that lemma. -/
theorem reubStrip_headD_ne_zero (xs : List Byte) : (reubStrip xs).headD 1 ≠ 0 := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    by_cases h : b = 0
    · subst h; rw [reubStrip_cons_zero]; exact ih
    · rw [reubStrip_cons_ne b bs h]; simpa using h

theorem reubStrip_length_le (xs : List Byte) : (reubStrip xs).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    by_cases h : b = 0
    · subst h; rw [reubStrip_cons_zero]; simp; omega
    · rw [reubStrip_cons_ne b bs h]

/-- The stripped list is the suffix of the input starting past the leading
    zeros — the form the machine layer needs, since the strip loop advances a
    cursor rather than building a list. -/
theorem reubStrip_eq_drop (xs : List Byte) :
    reubStrip xs = xs.drop (xs.length - (reubStrip xs).length) := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    by_cases h : b = 0
    · subst h
      rw [reubStrip_cons_zero]
      have hle := reubStrip_length_le bs
      rw [List.length_cons]
      rw [show bs.length + 1 - (reubStrip bs).length
            = (bs.length - (reubStrip bs).length) + 1 from by omega]
      rw [List.drop_succ_cons]
      exact ih
    · rw [reubStrip_cons_ne b bs h]
      simp

theorem reubStrip_eq_nil_iff (xs : List Byte) :
    reubStrip xs = [] ↔ ∀ b ∈ xs, b = 0 := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    by_cases h : b = 0
    · subst h
      rw [reubStrip_cons_zero]
      simp [ih]
    · rw [reubStrip_cons_ne b bs h]
      constructor
      · intro hc; exact absurd hc (by simp)
      · intro hall; exact absurd (hall b (by simp)) h

/-- Stripping does not change the scalar the bytes denote. -/
theorem fromBytesBE_reubStrip (xs : List Byte) :
    Nat.fromBytesBE (reubStrip xs) = Nat.fromBytesBE xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : b = 0
    · subst h
      rw [reubStrip_cons_zero, ih]
      simp [Nat.fromBytesBE]
    · rw [reubStrip_cons_ne b bs h]

/-- **The strip produces exactly the minimal big-endian form.**  This is what
    makes the machine-level post a statement about the *scalar* rather than
    about a byte-shuffling coincidence. -/
theorem reubStrip_eq_toBytesBE (xs : List Byte) :
    reubStrip xs = Nat.toBytesBE (Nat.fromBytesBE xs) := by
  rw [← fromBytesBE_reubStrip]
  exact (Nat.toBytesBE_fromBytesBE_of_canonical _ (reubStrip_headD_ne_zero xs)).symm

/-- The bytes `rlp_encode_uint_be` writes to its output buffer. -/
def reubOut (xs : List Byte) : List Byte := encodeBytes (reubStrip xs)

/-- **Canonical scalar encoding.**  The routine emits the RLP encoding of the
    scalar its input denotes, in minimal big-endian form — i.e. it agrees with
    `rlp.encode(Uint(v))` of the reference, not merely with some encoding of
    some byte string. -/
theorem reubOut_eq_encode_toBytesBE (xs : List Byte) :
    reubOut xs = encodeBytes (Nat.toBytesBE (Nat.fromBytesBE xs)) := by
  rw [reubOut, reubStrip_eq_toBytesBE]

/-! ### The three canonical-form corollaries, off the model side -/

/-- Zero — however many leading zero bytes it is spelled with — encodes as the
    RLP empty string `0x80`. -/
theorem reubOut_of_all_zero (xs : List Byte) (h : ∀ b ∈ xs, b = 0) :
    reubOut xs = [BitVec.ofNat 8 0x80] := by
  rw [reubOut, (reubStrip_eq_nil_iff xs).2 h, encodeBytes_nil]

/-- A scalar below `0x80` is its own encoding (no `0x81` prefix). -/
theorem reubOut_single_small (xs : List Byte) (b : Byte)
    (hstrip : reubStrip xs = [b]) (hb : b.toNat < 0x80) :
    reubOut xs = [b] := by
  rw [reubOut, hstrip, encodeBytes_single_small b hb]

/-- A single byte at or above `0x80` takes the `0x81` prefix. -/
theorem reubOut_single_large (xs : List Byte) (b : Byte)
    (hstrip : reubStrip xs = [b]) (hb : ¬ b.toNat < 0x80) :
    reubOut xs = [BitVec.ofNat 8 0x81, b] := by
  rw [reubOut, hstrip, encodeBytes_single_large b hb]

/-- **The model's payload never begins with a zero byte.**  A statement about
    `reubStrip`, i.e. about the model — nothing is claimed here about what the
    machine writes, since no triple covers the payload yet.

    `headD 1` makes the empty case hold trivially (`reubStrip` is `[]` when the
    input is all zeros, and the default is nonzero), so this must not be read as
    "the payload is nonempty" — for the all-zeros input the payload *is* empty
    and `reubOut_of_all_zero` is the statement that applies. -/
theorem reubOut_no_leading_zero (xs : List Byte) :
    (reubStrip xs).headD 1 ≠ 0 :=
  reubStrip_headD_ne_zero xs

/-! ### Output length, and the short-form domain

    The routine writes `1 + (reubStrip xs).length` bytes in the header path and
    exactly 1 in the two single-byte paths, so the buffer requirement is
    `xs.length + 1` — the capacity the ABI already documents. -/

/-- The short-form header the machine writes at [21]-[23] agrees with
    `encodeBytes` exactly when the stripped payload is at least two bytes and at
    most 55.  Below two bytes the two single-byte tails handle it; above 55 the
    routine is out of domain (see the module docstring). -/
theorem reubOut_short_form (xs : List Byte) (hlo : 2 ≤ (reubStrip xs).length)
    (hhi : (reubStrip xs).length ≤ 55) :
    reubOut xs
      = BitVec.ofNat 8 (0x80 + (reubStrip xs).length) :: reubStrip xs := by
  rw [reubOut, encodeBytes_short_of_length_ne_one _ hhi (by omega)]
  rfl

theorem reubOut_length_le (xs : List Byte) (h : xs.length ≤ 55) :
    (reubOut xs).length ≤ xs.length + 1 := by
  have hle := reubStrip_length_le xs
  rcases hs : reubStrip xs with _ | ⟨b, tl⟩
  · rw [reubOut, hs, encodeBytes_nil]; simp
  · rcases tl with _ | ⟨c, tl'⟩
    · by_cases hb : b.toNat < 0x80
      · rw [reubOut_single_small xs b hs hb]
        simp
      · rw [reubOut_single_large xs b hs hb]
        rw [hs] at hle; simp at hle ⊢; omega
    · rw [reubOut_short_form xs (by rw [hs]; simp) (by omega)]
      rw [hs] at hle ⊢
      simpa using hle

/-! ## §1b  The strip loop's trip count, indexed the way the machine is

    Instructions [2]-[7] walk a cursor rather than building a list, so the loop
    invariant needs the leading-zero count as a function of `(offset, remaining)`
    against the *region* bytes.  `reubZeros` is that function, and
    `reubStrip_drop_eq` is the bridge back to §1 — which is what keeps the
    machine post stated in terms of `reubStrip`/`reubOut` rather than in terms
    of the loop's own cursor arithmetic. -/

/-- Leading zero bytes among the `n` bytes of `xs` starting at offset `si`. -/
def reubZeros (xs : List Byte) (si : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if getByteAt xs si = 0 then reubZeros xs (si + 1) n + 1 else 0

@[simp] theorem reubZeros_zero (xs : List Byte) (si : Nat) : reubZeros xs si 0 = 0 := rfl

theorem reubZeros_succ_of_zero (xs : List Byte) (si n : Nat) (h : getByteAt xs si = 0) :
    reubZeros xs si (n + 1) = reubZeros xs (si + 1) n + 1 := by
  simp [reubZeros, h]

theorem reubZeros_succ_of_ne (xs : List Byte) (si n : Nat) (h : getByteAt xs si ≠ 0) :
    reubZeros xs si (n + 1) = 0 := by
  rw [show reubZeros xs si (n + 1)
        = if getByteAt xs si = 0 then reubZeros xs (si + 1) n + 1 else 0 from rfl,
      if_neg h]

theorem reubZeros_le (xs : List Byte) (si n : Nat) : reubZeros xs si n ≤ n := by
  induction n generalizing si with
  | zero => simp
  | succ k ih =>
    by_cases h : getByteAt xs si = 0
    · rw [reubZeros_succ_of_zero xs si k h]
      have := ih (si := si + 1); omega
    · rw [reubZeros_succ_of_ne xs si k h]; omega

/-- Every byte the loop steps over is zero — the loop's own postcondition on the
    prefix it consumed. -/
theorem reubZeros_byte_zero (xs : List Byte) (si n k : Nat) (hk : k < reubZeros xs si n) :
    getByteAt xs (si + k) = 0 := by
  induction n generalizing si k with
  | zero => simp at hk
  | succ m ih =>
    by_cases h : getByteAt xs si = 0
    · rw [reubZeros_succ_of_zero xs si m h] at hk
      cases k with
      | zero => simpa using h
      | succ k' =>
        have := ih (si := si + 1) (k := k') (by omega)
        rw [show si + (k' + 1) = si + 1 + k' from by omega]
        exact this
    · rw [reubZeros_succ_of_ne xs si m h] at hk; omega

/-- If the loop stopped short of exhausting the window, the byte it stopped on is
    nonzero — the fact the `BNE` at [4] hands to the header path. -/
theorem reubZeros_stop_ne (xs : List Byte) (si n : Nat) (hlt : reubZeros xs si n < n) :
    getByteAt xs (si + reubZeros xs si n) ≠ 0 := by
  induction n generalizing si with
  | zero => simp at hlt
  | succ m ih =>
    by_cases h : getByteAt xs si = 0
    · rw [reubZeros_succ_of_zero xs si m h] at hlt ⊢
      have hm : reubZeros xs (si + 1) m < m := by omega
      have := ih (si := si + 1) hm
      rw [show si + (reubZeros xs (si + 1) m + 1) = si + 1 + reubZeros xs (si + 1) m from by omega]
      exact this
    · rw [reubZeros_succ_of_ne xs si m h]
      simpa using h

/-! ### The three facts a loop round needs

    The strip loop's invariant carries the single inequality
    `j ≤ reubZeros xs si n` rather than a `∀ k < j` conjunction, because these
    three lemmas turn that inequality into exactly what each of the round's
    three outcomes has to establish. -/

/-- **Continue arm.**  A round that reads a zero byte and has not exhausted the
    window strictly advances the bound, so the invariant re-establishes. -/
theorem reubZeros_gt_of_zero (xs : List Byte) (si n j : Nat)
    (hj : j ≤ reubZeros xs si n) (hjn : j < n) (hz : getByteAt xs (si + j) = 0) :
    j < reubZeros xs si n := by
  rcases Nat.lt_or_ge j (reubZeros xs si n) with h | h
  · exact h
  · have heq : reubZeros xs si n = j := by omega
    have hlt : reubZeros xs si n < n := by omega
    exact absurd (heq ▸ hz) (by simpa [heq] using reubZeros_stop_ne xs si n hlt)

/-- **Break arm.**  A round that reads a nonzero byte pins the count exactly. -/
theorem reubZeros_eq_of_ne (xs : List Byte) (si n j : Nat)
    (hj : j ≤ reubZeros xs si n) (hne : getByteAt xs (si + j) ≠ 0) :
    reubZeros xs si n = j := by
  rcases Nat.lt_or_ge j (reubZeros xs si n) with h | h
  · exact absurd (reubZeros_byte_zero xs si n j h) hne
  · omega

/-- **Exhaustion arm.**  Reaching the end of the window means every byte was
    zero, so the stripped payload is empty. -/
theorem reubZeros_eq_self (xs : List Byte) (si n : Nat) (hj : n ≤ reubZeros xs si n) :
    reubZeros xs si n = n :=
  Nat.le_antisymm (reubZeros_le xs si n) hj

/-- **Bridge to §1.**  Stripping the tail of the buffer from `si` is the same as
    dropping the leading zeros the loop counted. -/
theorem reubStrip_drop_eq (xs : List Byte) (si n : Nat) (h : si + n = xs.length) :
    reubStrip (xs.drop si) = xs.drop (si + reubZeros xs si n) := by
  induction n generalizing si with
  | zero =>
    have hsi : si = xs.length := by omega
    subst hsi
    simp
  | succ m ih =>
    have hsi : si < xs.length := by omega
    have hget : getByteAt xs si = xs[si]'hsi := by
      simp [getByteAt, hsi]
    rw [List.drop_eq_getElem_cons hsi]
    by_cases hz : getByteAt xs si = 0
    · rw [show (xs[si]'hsi) = 0 from by rw [← hget]; exact hz,
          reubStrip_cons_zero, ih (si + 1) (by omega),
          reubZeros_succ_of_zero xs si m hz,
          show si + (reubZeros xs (si + 1) m + 1) = si + 1 + reubZeros xs (si + 1) m from by omega]
    · have hne : (xs[si]'hsi) ≠ 0 := by rw [← hget]; exact hz
      rw [reubStrip_cons_ne _ _ hne, reubZeros_succ_of_ne xs si m hz, Nat.add_zero]
      exact (List.drop_eq_getElem_cons hsi).symm

/-- The window the loop leaves behind is exactly the stripped payload, so its
    length is the payload length the header byte must record. -/
theorem reubZeros_sub_length (xs : List Byte) (si n : Nat) (h : si + n = xs.length) :
    n - reubZeros xs si n = (reubStrip (xs.drop si)).length := by
  rw [reubStrip_drop_eq xs si n h, List.length_drop]
  have := reubZeros_le xs si n
  omega

/-! ## §2  Guest layout

    Stated at the `#guard`-tied symbolic `GuestAddrs.rlp_encode_uint_be` base,
    the same convention as `RlpSpliceHelperSpec.rlpItemSizeBase` — so the spec
    is about the linked routine and not about a floating `∀ base` copy. -/

/-- Guest entry of `rlp_encode_uint_be`. -/
def reubBase : Word := BitVec.ofNat 64 GuestAddrs.rlp_encode_uint_be

/-- The `rlp_encode_uint_be` body at its linked guest address. -/
abbrev reubCode : CodeReq := CodeReq.ofProg reubBase rlpEncodeUintBe_prog

theorem reub_prog_length : rlpEncodeUintBe_prog.length = 35 := by decide

/-- Code-membership for instruction `k`, addressed as `reubBase + OFF`. -/
local macro "reubmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr reubBase rlpEncodeUintBe_prog $k _
        (by rw [reub_prog_length]; norm_num)
        (by rw [reub_prog_length]; norm_num) (by rfl)))

/-! ## §3  The all-zeros tail ([8]-[11])

    Reached from the strip loop's exhaustion exit: every input byte was zero, so
    the scalar is zero and RLP encodes it as the empty string `0x80`.  This is
    `reubOut_of_all_zero` on the machine. -/

set_option maxRecDepth 8000 in
/-- `reubBase+32 → ra &&& ~~~1`: store `0x80` at `out[0]`, return `a0 = 1`. -/
theorem reubEmptyTail (outPtr raVal v28 v10 : Word) (oldOut : List Byte)
    (hoalign : outPtr.toNat % 8 = 0) (holen : 0 < oldOut.length)
    (hoover : outPtr.toNat < 2 ^ 64)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin 4 (reubBase + 32) (raVal &&& ~~~1) reubCode
      (((.x28 : Reg) ↦ᵣ v28) ** ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x10 : Reg) ↦ᵣ v10) **
       ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion outPtr oldOut)
      (((.x28 : Reg) ↦ᵣ (128 : Word)) ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
       bytesRegion outPtr (oldOut.set 0 (BitVec.ofNat 8 0x80))) := by
  have haddr0 : outPtr + BitVec.ofNat 64 0 = outPtr := by bv_omega
  have hLI28 := li_spec_gen_within .x28 v28 (128 : Word) (reubBase + 32) (by decide)
  have hSB := bytesRegion_sb_within .x12 .x28 outPtr (128 : Word) (reubBase + 36)
    oldOut 0 hoalign holen (by omega) (by rw [haddr0]; exact hovalid)
  rw [haddr0, show ((128 : Word).truncate 8) = BitVec.ofNat 8 0x80 from by decide] at hSB
  have hLI10 := li_spec_gen_within .x10 v10 (1 : Word) (reubBase + 40) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (reubBase + 44)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at hRet
  runBlock hLI28 hSB hLI10 hRet

/-! ## §4  The leading-zero strip loop ([2]-[7])

    A two-exit countdown loop, folded with `twoExitRetLoop_spec`: each round
    either BREAKS to `reubBase+48` (a nonzero byte — the payload starts here) or
    returns to the header with the cursor advanced; exhausting the window exits
    to `reubBase+32` (the all-zeros tail of §3).

    The invariant carries the single inequality `j ≤ reubZeros xs 0 n` rather
    than a `∀ k < j` conjunction; §1b's three round lemmas convert it into what
    each outcome must establish. -/

/-- Ambient registers and regions the strip loop leaves untouched. -/
def reubAmb (srcPtr outPtr raVal : Word) (oldOut : List Byte) : Assertion :=
  ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
  ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion outPtr oldOut

theorem pcFree_reubAmb (srcPtr outPtr raVal : Word) (oldOut : List Byte) :
    (reubAmb srcPtr outPtr raVal oldOut).pcFree := by
  unfold reubAmb; pcFree

/-- The strip loop's stable half after `j` rounds: cursor at `src+j`, counter
    `n-j`, the source region, and the ambient registers.

    Split out from `reubInvCore` so that `regOwn .x28` is the whole right factor
    of the invariant: the round proof has to name the scratch byte register's
    incoming value, and `cpsBranchWithin_of_forall_regIs_to_regOwn` only reaches
    a **trailing** `regOwn`.  Likewise `reubInv` keeps its pure bound as the
    outermost right factor so `cpsBranchWithin_pure_pre_right` can peel it
    without an intervening `xperm` reshape. -/
def reubStable (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n j : Nat) :
    Assertion :=
  ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 j)) **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - j)) **
  bytesRegion srcPtr xs **
  reubAmb srcPtr outPtr raVal oldOut

/-- `reubStable` plus ownership of the scratch byte register. -/
def reubInvCore (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n j : Nat) :
    Assertion :=
  reubStable srcPtr outPtr raVal xs oldOut n j ** regOwn .x28

/-- Strip-loop invariant after `j` rounds: `reubInvCore`, plus `j` bounded by the
    true leading-zero count. -/
def reubInv (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n j : Nat) :
    Assertion :=
  reubInvCore srcPtr outPtr raVal xs oldOut n j ** ⌜j ≤ reubZeros xs 0 n⌝

/-- The break post: the loop stopped at the first nonzero byte, whose offset is
    exactly the leading-zero count.  The stopped-on byte itself is not exposed —
    it is recoverable from `d < n` by `reubZeros_stop_ne`, and `[21]` overwrites
    `x28` immediately. -/
def reubBreakPost (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n : Nat) :
    Assertion :=
  fun h => ∃ d,
    (reubInvCore srcPtr outPtr raVal xs oldOut n d **
     ⌜d = reubZeros xs 0 n ∧ d < n⌝) h

/-- The exhaustion post: every byte was zero, so the stripped payload is empty
    and §3's tail is correct to write `0x80`. -/
def reubExhPost (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n : Nat) :
    Assertion :=
  reubInvCore srcPtr outPtr raVal xs oldOut n n ** ⌜reubZeros xs 0 n = n⌝

/-! ### Local arithmetic for the loop edges -/

/-- `ADDI x5, x5, 1` advances the source cursor. -/
private theorem reub_cur_up (srcPtr : Word) (j : Nat) :
    (srcPtr + BitVec.ofNat 64 j) + signExtend12 (1 : BitVec 12)
      = srcPtr + BitVec.ofNat 64 (j + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

/-- A byte's zero-extension is zero exactly when the byte is. -/
theorem zeroExtend_eq_zero_iff (b : BitVec 8) :
    (b.zeroExtend 64 = (0 : Word)) ↔ b = 0 := by
  constructor
  · intro h
    have hmod := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth] at hmod
    have hlt : b.toNat < 256 := b.isLt
    refine BitVec.eq_of_toNat_eq ?_
    rw [show (0 : Word).toNat = 0 from by decide] at hmod
    rw [show (0 : BitVec 8).toNat = 0 from by decide]
    omega
  · intro h; subst h; decide

/-! ### The round

    The round's control flow is decided by data the caller already fixed (`j`,
    `xs`), so the proof splits on `xs[j] = 0` FIRST and each arm is then a
    straight-line `runBlock` chain — rather than composing a branch and
    threading the `BNE`'s pure outcome through a `hperm` that would discard it.
    Instructions, all six: `BEQ` (falls through, counter nonzero), `LBU`,
    `BNE` (breaks iff the byte is nonzero), `ADDI`/`ADDI`/`JAL`. -/

set_option maxRecDepth 8000 in
/-- **One strip-loop round**, `j < n`: either BREAK to `reubBase+48` with the
    leading-zero count pinned at `j`, or advance to `reubBase+8` with the
    invariant at `j+1`. -/
theorem reubStripRound (srcPtr outPtr raVal : Word) (xs oldOut : List Byte)
    (n j : Nat) (hjn : j < n) (hnlen : n ≤ xs.length) (hn64 : n < 2 ^ 64)
    (hsalign : srcPtr.toNat % 8 = 0) (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin 6 (reubBase + 8) reubCode
      (reubInv srcPtr outPtr raVal xs oldOut n j)
      (reubBase + 48) (reubBreakPost srcPtr outPtr raVal xs oldOut n)
      (reubBase + 8) (reubInv srcPtr outPtr raVal xs oldOut n (j + 1)) := by
  have hjlen : j < xs.length := by omega
  have hget : getByteAt xs j = xs[j]'hjlen := by simp [getByteAt, hjlen]
  unfold reubInv reubInvCore
  refine cpsBranchWithin_pure_pre_right (fun hj => ?_)
  refine cpsBranchWithin_of_forall_regIs_to_regOwn (fun v28 => ?_)
  -- [2] `BEQ x6, x0, +24` — the counter is `n - j > 0`, so it falls through.
  have hcntne : BitVec.ofNat 64 (n - j) ≠ (0 : Word) := by
    obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
    rw [hm]; exact word_ofNat_succ_ne_zero m (by omega)
  have hbeq0 := beq_spec_gen_within .x6 .x0 (24 : BitVec 13)
    (BitVec.ofNat 64 (n - j)) (0 : Word) (reubBase + 8)
  rw [show reubBase + 8 + 4 = reubBase + 12 from by bv_omega] at hbeq0
  have hbeq := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hbeq0 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 hpure).2 hcntne))
  -- [3] `LBU x28, 0(x5)` — reads `xs[j]`.
  have hlbu := bytesRegion_lbu_within .x28 .x5 srcPtr v28 (reubBase + 12) xs j
    (by decide) hsalign hjlen (by omega) (hsvalid j (by omega))
  rw [show reubBase + 12 + 4 = reubBase + 16 from by bv_omega] at hlbu
  -- [4] `BNE x28, x0, +32`.
  have hbne0 := bne_spec_gen_within .x28 .x0 (32 : BitVec 13)
    ((xs[j]'hjlen).zeroExtend 64) (0 : Word) (reubBase + 16)
  rw [show reubBase + 16 + signExtend13 (32 : BitVec 13) = reubBase + 48 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega,
      show reubBase + 16 + 4 = reubBase + 20 from by bv_omega] at hbne0
  by_cases hz : (xs[j]'hjlen) = 0
  · -- ===== zero byte: the round continues =====
    have hbzero : ((xs[j]'hjlen).zeroExtend 64) = (0 : Word) :=
      (zeroExtend_eq_zero_iff _).2 hz
    have hbne := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      (cpsBranchWithin_ntakenPath hbne0 (fun _ hQt => by
        obtain ⟨_, _, _, _, _, hpure⟩ := hQt
        exact absurd hbzero ((sepConj_pure_right _).1 hpure).2))
    -- [5] `ADDI x5, x5, 1`; [6] `ADDI x6, x6, -1`; [7] `JAL x0, -20`.
    have haddi5 := addi_spec_gen_same_within .x5 (srcPtr + BitVec.ofNat 64 j)
      (1 : BitVec 12) (reubBase + 20) (by decide)
    rw [reub_cur_up srcPtr j,
        show reubBase + 20 + 4 = reubBase + 24 from by bv_omega] at haddi5
    have haddi6 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (n - j))
      (-1 : BitVec 12) (reubBase + 24) (by decide)
    rw [show BitVec.ofNat 64 (n - j) + signExtend12 (-1 : BitVec 12)
          = BitVec.ofNat 64 (n - (j + 1)) from by
          rw [show n - j = (n - (j + 1)) + 1 from by omega]
          exact word_ofNat_succ_dec (n - (j + 1)),
        show reubBase + 24 + 4 = reubBase + 28 from by bv_omega] at haddi6
    have hjal := jal_x0_spec_gen_within (-20 : BitVec 21) (reubBase + 28)
    rw [show reubBase + 28 + signExtend21 (-20 : BitVec 21) = reubBase + 8 from by
          rw [show signExtend21 (-20 : BitVec 21) = -(20 : Word) from by decide]
          bv_omega] at hjal
    have hround : cpsTripleWithin 6 (reubBase + 8) (reubBase + 8) reubCode
        (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 j)) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - j)) **
         ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcPtr xs **
         ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
         ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr oldOut)
        (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 (j + 1))) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - (j + 1))) **
         ((.x28 : Reg) ↦ᵣ ((xs[j]'hjlen).zeroExtend 64)) ** bytesRegion srcPtr xs **
         ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
         ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr oldOut) := by
      runBlock hbeq hlbu hbne haddi5 haddi6 hjal
    have hlt : j < reubZeros xs 0 n :=
      reubZeros_gt_of_zero xs 0 n j (by simpa using hj) hjn
        (by rw [Nat.zero_add, hget]; exact hz)
    refine cpsBranchWithin_weaken (fun h hp => ?_) (fun _ hp => hp) (fun h hp => ?_)
      (cpsTripleWithin_as_cpsBranchWithin_right (reubBase + 48)
        (reubBreakPost srcPtr outPtr raVal xs oldOut n) hround)
    · unfold reubStable reubAmb at hp; xperm_hyp hp
    · refine (sepConj_pure_right h).2 ⟨?_, by omega⟩
      unfold reubStable reubAmb
      have hp2 : ((((.x28 : Reg) ↦ᵣ ((xs[j]'hjlen).zeroExtend 64)) **
          ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 (j + 1))) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - (j + 1))) **
          bytesRegion srcPtr xs **
          ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion outPtr oldOut)) h := by xperm_hyp hp
      have hp3 := sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x) h hp2
      xperm_hyp hp3
  · -- ===== nonzero byte: the round breaks =====
    have hbne := cpsTripleWithin_weaken (fun _ hp => hp)
      (fun h hp => sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
      (cpsBranchWithin_takenPath hbne0 (fun _ hQf => by
        obtain ⟨_, _, _, _, _, hpure⟩ := hQf
        exact absurd ((zeroExtend_eq_zero_iff _).1
          ((sepConj_pure_right _).1 hpure).2) hz))
    have hbreak : cpsTripleWithin 3 (reubBase + 8) (reubBase + 48) reubCode
        (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 j)) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - j)) **
         ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcPtr xs **
         ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
         ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr oldOut)
        (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 j)) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - j)) **
         ((.x28 : Reg) ↦ᵣ ((xs[j]'hjlen).zeroExtend 64)) ** bytesRegion srcPtr xs **
         ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
         ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion outPtr oldOut) := by
      runBlock hbeq hlbu hbne
    have heq : reubZeros xs 0 n = j :=
      reubZeros_eq_of_ne xs 0 n j (by simpa using hj)
        (by rw [Nat.zero_add, hget]; exact hz)
    refine cpsBranchWithin_mono_nSteps (by omega)
      (cpsBranchWithin_weaken (fun h hp => ?_) (fun h hp => ?_) (fun _ hp => hp)
        (cpsTripleWithin_as_cpsBranchWithin_left (reubBase + 8)
          (reubInv srcPtr outPtr raVal xs oldOut n (j + 1)) hbreak))
    · unfold reubStable reubAmb at hp; xperm_hyp hp
    · refine ⟨j, (sepConj_pure_right h).2 ⟨?_, heq.symm, hjn⟩⟩
      unfold reubInvCore reubStable reubAmb
      have hp2 : ((((.x28 : Reg) ↦ᵣ ((xs[j]'hjlen).zeroExtend 64)) **
          ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 j)) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - j)) **
          bytesRegion srcPtr xs **
          ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion outPtr oldOut)) h := by xperm_hyp hp
      have hp3 := sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x) h hp2
      xperm_hyp hp3

set_option maxRecDepth 8000 in
/-- **Strip-loop exhaustion** ([2] with the counter at zero, `j = n`): the window
    is used up, so every byte was zero and the count is pinned at `n`.

    The invariant's `n ≤ reubZeros xs 0 n` is upgraded to equality here rather
    than in §5, since `reubZeros_eq_self` is exactly the missing half. -/
theorem reubStripExh (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n : Nat) :
    cpsTripleWithin 1 (reubBase + 8) (reubBase + 32) reubCode
      (reubInv srcPtr outPtr raVal xs oldOut n n)
      (reubExhPost srcPtr outPtr raVal xs oldOut n) := by
  have hzero : BitVec.ofNat 64 (n - n) = (0 : Word) := by rw [Nat.sub_self]; decide
  have hbeq0 := beq_spec_gen_within .x6 .x0 (24 : BitVec 13)
    (BitVec.ofNat 64 (n - n)) (0 : Word) (reubBase + 8)
  rw [show reubBase + 8 + signExtend13 (24 : BitVec 13) = reubBase + 32 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]
        bv_omega] at hbeq0
  have hbeq := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hbeq0 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      exact absurd hzero ((sepConj_pure_right _).1 hpure).2))
  unfold reubInv reubExhPost reubInvCore
  -- No `cpsTripleWithin_pure_pre_right` exists (only the branch twin), so the
  -- trailing pure factor is commuted to the front and peeled on the left.
  refine cpsTripleWithin_weaken (fun h hp => (sepConj_comm h).1 hp) (fun _ hp => hp) ?_
  refine cpsTripleWithin_pure_pre (fun hj => ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v28 => ?_)
  have hcore : cpsTripleWithin 1 (reubBase + 8) (reubBase + 32) reubCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) **
       ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
       ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcPtr xs **
       ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr oldOut)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) **
       ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
       ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcPtr xs **
       ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr oldOut) := by
    (runBlock hbeq)
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hcore
  · unfold reubStable reubAmb at hp; xperm_hyp hp
  · refine (sepConj_pure_right h).2 ⟨?_, reubZeros_eq_self xs 0 n hj⟩
    unfold reubStable reubAmb
    have hp2 : ((((.x28 : Reg) ↦ᵣ v28) **
        ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) **
        bytesRegion srcPtr xs **
        ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion outPtr oldOut)) h := by xperm_hyp hp
    have hp3 := sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x) h hp2
    xperm_hyp hp3

/-- **The strip loop, folded** ([2]-[7]): from the header, either BREAK to
    `reubBase+48` with the leading-zero count pinned, or exhaust the window to
    `reubBase+32` (the all-zeros tail of §3).  `n * 6 + 1` steps: `n` rounds of
    six instructions plus the final `BEQ`. -/
theorem reubStripLoop (srcPtr outPtr raVal : Word) (xs oldOut : List Byte)
    (n : Nat) (hnlen : n ≤ xs.length) (hn64 : n < 2 ^ 64)
    (hsalign : srcPtr.toNat % 8 = 0) (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true) :
    cpsBranchWithin (n * 6 + 1) (reubBase + 8) reubCode
      (reubInv srcPtr outPtr raVal xs oldOut n 0)
      (reubBase + 48) (reubBreakPost srcPtr outPtr raVal xs oldOut n)
      (reubBase + 32) (reubExhPost srcPtr outPtr raVal xs oldOut n) :=
  twoExitRetLoop_spec n 6 1 (reubInv srcPtr outPtr raVal xs oldOut n)
    (fun j hj => reubStripRound srcPtr outPtr raVal xs oldOut n j hj hnlen hn64
      hsalign hsover hsvalid)
    (reubStripExh srcPtr outPtr raVal xs oldOut n)

/-! ## §5  The single-byte dispatch ([12]-[17]) and its tail ([18]-[20])

    `[14] BNE x6, x28` sends any payload length other than one to the header
    path at `reubBase+84`, and `[17] BGEU x29, x30` sends a single byte `≥ 0x80`
    there too — the header path then writes `0x81` ahead of it.  Only a single
    byte *below* `0x80` reaches [18], where it is stored as itself: that is
    `reubOut_single_small` on the machine, and `[12] MV x31, x6` is what carries
    the payload length across to the header path.

    Three straight-line triples rather than one branch-shaped dispatch, because
    the whole-routine proof has to case-split on the same condition anyway — the
    *model* splits there too (`encodeBytes_single_small` versus
    `encodeBytes_short_of_length_ne_one`). -/

/-- The low byte of a zero-extended byte is the byte. -/
private theorem truncate_zeroExtend_byte (b : Byte) :
    ((b.zeroExtend 64).truncate 8) = b := by
  apply BitVec.eq_of_toNat_eq
  have hb : b.toNat < 2 ^ 8 := b.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt hb]

/-- A payload length other than one is not the `1` that `[13]` materialises. -/
private theorem reub_ofNat_ne_one (L : Nat) (hL : L ≠ 1) (hb : L < 2 ^ 64) :
    BitVec.ofNat 64 L ≠ (1 : Word) := by
  intro heq
  have h2 := congrArg BitVec.toNat heq
  rw [show (1 : Word).toNat = 1 from by decide] at h2
  simp only [BitVec.toNat_ofNat] at h2
  omega

/-- `[17]`'s guard, below the boundary: a byte under `0x80` compares less. -/
private theorem ult_zeroExtend_of_lt (b : Byte) (h : b.toNat < 128) :
    BitVec.ult (b.zeroExtend 64) (128 : Word) = true := by
  have hb : b.toNat < 2 ^ 8 := b.isLt
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_setWidth,
    show (128 : Word).toNat = 128 from by decide]
  omega

/-- `[17]`'s guard, at or above the boundary. -/
private theorem ult_zeroExtend_of_ge (b : Byte) (h : 128 ≤ b.toNat) :
    BitVec.ult (b.zeroExtend 64) (128 : Word) = false := by
  have hb : b.toNat < 2 ^ 8 := b.isLt
  simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_setWidth,
    show (128 : Word).toNat = 128 from by decide]
  omega

/-- What the dispatch sees at `reubBase+48`: the cursor at the payload start,
    the payload length still in `x6`, and the four scratch registers explicit
    (the dispatch is straight-line, so nothing here has to be abstracted). -/
def reubDispPre (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n d : Nat)
    (v28 v29 v30 v31 : Word) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
  ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
  ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
  bytesRegion srcPtr xs **
  reubAmb srcPtr outPtr raVal oldOut

/-- What the header path at `reubBase+84` receives.  `x29`/`x30` stay parametric
    because the two routes in differ there: the `len ≠ 1` route never reaches
    [15]/[16], while the `byte ≥ 0x80` route leaves the byte and `0x80` behind. -/
def reubHeaderPre (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n d : Nat)
    (v29 v30 : Word) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
  ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x29 : Reg) ↦ᵣ v29) **
  ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
  bytesRegion srcPtr xs **
  reubAmb srcPtr outPtr raVal oldOut

/-- What the single-small-byte tail at `reubBase+72` receives. -/
def reubSinglePre (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n d : Nat)
    (b : Byte) : Assertion :=
  ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
  ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x29 : Reg) ↦ᵣ (b.zeroExtend 64)) **
  ((.x30 : Reg) ↦ᵣ (128 : Word)) ** ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
  bytesRegion srcPtr xs **
  reubAmb srcPtr outPtr raVal oldOut

set_option maxRecDepth 8000 in
/-- **Dispatch, `len ≠ 1`** ([12]-[14], `BNE` taken): straight to the header
    path.  `x29`/`x30` are untouched, which is why `reubHeaderPre` leaves them
    parametric. -/
theorem reubDispHeaderLong (srcPtr outPtr raVal : Word) (xs oldOut : List Byte)
    (n d : Nat) (v28 v29 v30 v31 : Word)
    (hL : n - d ≠ 1) (hn64 : n < 2 ^ 64) :
    cpsTripleWithin 3 (reubBase + 48) (reubBase + 84) reubCode
      (reubDispPre srcPtr outPtr raVal xs oldOut n d v28 v29 v30 v31)
      (reubHeaderPre srcPtr outPtr raVal xs oldOut n d v29 v30) := by
  have hMV := mv_spec_gen_within .x31 .x6 (BitVec.ofNat 64 (n - d)) v31
    (reubBase + 48) (by decide)
  rw [show reubBase + 48 + 4 = reubBase + 52 from by bv_omega] at hMV
  have hLI := li_spec_gen_within .x28 v28 (1 : Word) (reubBase + 52) (by decide)
  rw [show reubBase + 52 + 4 = reubBase + 56 from by bv_omega] at hLI
  have hbne0 := bne_spec_gen_within .x6 .x28 (28 : BitVec 13)
    (BitVec.ofNat 64 (n - d)) (1 : Word) (reubBase + 56)
  rw [show reubBase + 56 + signExtend13 (28 : BitVec 13) = reubBase + 84 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        bv_omega] at hbne0
  have hbne := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hbne0 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      exact absurd ((sepConj_pure_right _).1 hpure).2
        (reub_ofNat_ne_one (n - d) hL (by omega))))
  unfold reubDispPre reubHeaderPre reubAmb
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 3 (reubBase + 48) (reubBase + 84) reubCode
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut)
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x28 : Reg) ↦ᵣ (1 : Word)) **
         ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut) from by
      (runBlock hMV hLI hbne))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **Dispatch, `len = 1` and the byte is `≥ 0x80`** ([12]-[17], `BGEU` taken):
    the header path writes `0x81` ahead of it. -/
theorem reubDispHeaderLarge (srcPtr outPtr raVal : Word) (xs oldOut : List Byte)
    (n d : Nat) (v28 v29 v30 v31 : Word) (hdlen : d < xs.length)
    (hL : n - d = 1)
    (hlarge : 128 ≤ (xs[d]'hdlen).toNat)
    (hsalign : srcPtr.toNat % 8 = 0) (hsover : srcPtr.toNat + d < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcPtr + BitVec.ofNat 64 d) = true) :
    cpsTripleWithin 6 (reubBase + 48) (reubBase + 84) reubCode
      (reubDispPre srcPtr outPtr raVal xs oldOut n d v28 v29 v30 v31)
      (reubHeaderPre srcPtr outPtr raVal xs oldOut n d
        ((xs[d]'hdlen).zeroExtend 64) (128 : Word)) := by
  have hone : BitVec.ofNat 64 (n - d) = (1 : Word) := by rw [hL]; decide
  have hMV := mv_spec_gen_within .x31 .x6 (BitVec.ofNat 64 (n - d)) v31
    (reubBase + 48) (by decide)
  rw [show reubBase + 48 + 4 = reubBase + 52 from by bv_omega] at hMV
  have hLI := li_spec_gen_within .x28 v28 (1 : Word) (reubBase + 52) (by decide)
  rw [show reubBase + 52 + 4 = reubBase + 56 from by bv_omega] at hLI
  have hbne0 := bne_spec_gen_within .x6 .x28 (28 : BitVec 13)
    (BitVec.ofNat 64 (n - d)) (1 : Word) (reubBase + 56)
  rw [show reubBase + 56 + 4 = reubBase + 60 from by bv_omega] at hbne0
  have hbne := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hbne0 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      exact absurd hone ((sepConj_pure_right _).1 hpure).2))
  have hlbu := bytesRegion_lbu_within .x29 .x5 srcPtr v29 (reubBase + 60) xs d
    (by decide) hsalign hdlen (by omega) hsvalid
  rw [show reubBase + 60 + 4 = reubBase + 64 from by bv_omega] at hlbu
  have hLI30 := li_spec_gen_within .x30 v30 (128 : Word) (reubBase + 64) (by decide)
  rw [show reubBase + 64 + 4 = reubBase + 68 from by bv_omega] at hLI30
  have hbgeu0 := bgeu_spec_gen_within .x29 .x30 (16 : BitVec 13)
    ((xs[d]'hdlen).zeroExtend 64) (128 : Word) (reubBase + 68)
  rw [show reubBase + 68 + signExtend13 (16 : BitVec 13) = reubBase + 84 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]
        bv_omega] at hbgeu0
  have hbgeu := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_takenPath hbgeu0 (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQf
      have := ((sepConj_pure_right _).1 hpure).2
      rw [ult_zeroExtend_of_ge _ hlarge] at this
      exact absurd this (by simp)))
  unfold reubDispPre reubHeaderPre reubAmb
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 6 (reubBase + 48) (reubBase + 84) reubCode
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut)
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x28 : Reg) ↦ᵣ (1 : Word)) **
         ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x29 : Reg) ↦ᵣ ((xs[d]'hdlen).zeroExtend 64)) **
         ((.x30 : Reg) ↦ᵣ (128 : Word)) **
         bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut) from by
      (runBlock hMV hLI hbne hlbu hLI30 hbgeu))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **Dispatch, `len = 1` and the byte is `< 0x80`** ([12]-[17], `BGEU` falls
    through): the byte encodes as itself, so §5's tail stores it raw. -/
theorem reubDispSmallSingle (srcPtr outPtr raVal : Word) (xs oldOut : List Byte)
    (n d : Nat) (v28 v29 v30 v31 : Word) (hdlen : d < xs.length)
    (hL : n - d = 1)
    (hsmall : (xs[d]'hdlen).toNat < 128)
    (hsalign : srcPtr.toNat % 8 = 0) (hsover : srcPtr.toNat + d < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcPtr + BitVec.ofNat 64 d) = true) :
    cpsTripleWithin 6 (reubBase + 48) (reubBase + 72) reubCode
      (reubDispPre srcPtr outPtr raVal xs oldOut n d v28 v29 v30 v31)
      (reubSinglePre srcPtr outPtr raVal xs oldOut n d (xs[d]'hdlen)) := by
  have hone : BitVec.ofNat 64 (n - d) = (1 : Word) := by rw [hL]; decide
  have hMV := mv_spec_gen_within .x31 .x6 (BitVec.ofNat 64 (n - d)) v31
    (reubBase + 48) (by decide)
  rw [show reubBase + 48 + 4 = reubBase + 52 from by bv_omega] at hMV
  have hLI := li_spec_gen_within .x28 v28 (1 : Word) (reubBase + 52) (by decide)
  rw [show reubBase + 52 + 4 = reubBase + 56 from by bv_omega] at hLI
  have hbne0 := bne_spec_gen_within .x6 .x28 (28 : BitVec 13)
    (BitVec.ofNat 64 (n - d)) (1 : Word) (reubBase + 56)
  rw [show reubBase + 56 + 4 = reubBase + 60 from by bv_omega] at hbne0
  have hbne := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hbne0 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      exact absurd hone ((sepConj_pure_right _).1 hpure).2))
  have hlbu := bytesRegion_lbu_within .x29 .x5 srcPtr v29 (reubBase + 60) xs d
    (by decide) hsalign hdlen (by omega) hsvalid
  rw [show reubBase + 60 + 4 = reubBase + 64 from by bv_omega] at hlbu
  have hLI30 := li_spec_gen_within .x30 v30 (128 : Word) (reubBase + 64) (by decide)
  rw [show reubBase + 64 + 4 = reubBase + 68 from by bv_omega] at hLI30
  have hbgeu0 := bgeu_spec_gen_within .x29 .x30 (16 : BitVec 13)
    ((xs[d]'hdlen).zeroExtend 64) (128 : Word) (reubBase + 68)
  rw [show reubBase + 68 + 4 = reubBase + 72 from by bv_omega] at hbgeu0
  have hbgeu := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    (cpsBranchWithin_ntakenPath hbgeu0 (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hpure⟩ := hQt
      have := ((sepConj_pure_right _).1 hpure).2
      rw [ult_zeroExtend_of_lt _ hsmall] at this
      exact absurd this (by simp)))
  unfold reubDispPre reubSinglePre reubAmb
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 6 (reubBase + 48) (reubBase + 72) reubCode
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) ** ((.x31 : Reg) ↦ᵣ v31) **
         ((.x28 : Reg) ↦ᵣ v28) ** ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut)
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x28 : Reg) ↦ᵣ (1 : Word)) **
         ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x29 : Reg) ↦ᵣ ((xs[d]'hdlen).zeroExtend 64)) **
         ((.x30 : Reg) ↦ᵣ (128 : Word)) **
         bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut) from by
      (runBlock hMV hLI hbne hlbu hLI30 hbgeu))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **The single-small-byte tail** ([18]-[20]), `reubBase+72 → ra &&& ~~~1`:
    store the byte itself and return `a0 = 1`. -/
theorem reubSingleTail (outPtr raVal v10 : Word) (b : Byte) (oldOut : List Byte)
    (hoalign : outPtr.toNat % 8 = 0) (holen : 0 < oldOut.length)
    (hoover : outPtr.toNat < 2 ^ 64)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin 3 (reubBase + 72) (raVal &&& ~~~1) reubCode
      (((.x12 : Reg) ↦ᵣ outPtr) ** ((.x29 : Reg) ↦ᵣ (b.zeroExtend 64)) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x1 : Reg) ↦ᵣ raVal) ** bytesRegion outPtr oldOut)
      (((.x12 : Reg) ↦ᵣ outPtr) ** ((.x29 : Reg) ↦ᵣ (b.zeroExtend 64)) **
       ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x1 : Reg) ↦ᵣ raVal) **
       bytesRegion outPtr (oldOut.set 0 b)) := by
  have haddr0 : outPtr + BitVec.ofNat 64 0 = outPtr := by bv_omega
  have hSB := bytesRegion_sb_within .x12 .x29 outPtr (b.zeroExtend 64) (reubBase + 72)
    oldOut 0 hoalign holen (by omega) (by rw [haddr0]; exact hovalid)
  rw [haddr0, truncate_zeroExtend_byte b] at hSB
  have hLI10 := li_spec_gen_within .x10 v10 (1 : Word) (reubBase + 76) (by decide)
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (reubBase + 80)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hRet
  runBlock hSB hLI10 hRet

/-! ## §6  The payload copy loop ([26]-[32])

    Instruction for instruction the same loop as `cu256_loop_spec_within`
    (`Rv64/RLP/ContentToU256Be.lean`) — `BEQ` head test, `LBU`/`SB`, three
    `ADDI`s, `JAL` back — under the register renaming

        counter `x28 → x6`,  src cursor `x7 → x5`,
        dst cursor `x6 → x29`,  scratch `x29 → x30`.

    So the post is `copyN` at the same offsets, reusing the verified core's
    definition and its lemmas rather than a second copy of them, and the proof
    is the same induction on the counter. -/

set_option maxRecDepth 8000 in
/-- One copy iteration ([27]-[31], `reubBase+108 → reubBase+128`): read
    `src[si]`, write it to `dst[di]`, advance both cursors, decrement. -/
theorem reubCopyBody (srcBase dstBase v30 v6 : Word)
    (srcBytes dstBytes : List Byte) (si di : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hsi : si < srcBytes.length) (hdi : di < dstBytes.length)
    (hsover : srcBase.toNat + si < 2 ^ 64) (hdover : dstBase.toNat + di < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true)
    (hdvalid : isValidByteAccess (dstBase + BitVec.ofNat 64 di) = true) :
    cpsTripleWithin 5 (reubBase + 108) (reubBase + 128) reubCode
      (((.x30 : Reg) ↦ᵣ v30) ** ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) ** ((.x6 : Reg) ↦ᵣ v6) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (((.x30 : Reg) ↦ᵣ (srcBytes[si]'hsi).zeroExtend 64) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
       ((.x6 : Reg) ↦ᵣ (v6 + signExtend12 (-1 : BitVec 12))) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi))) := by
  have lbu := bytesRegion_lbu_within .x30 .x5 srcBase v30 (reubBase + 108) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have sb := bytesRegion_sb_within .x29 .x30 dstBase ((srcBytes[si]'hsi).zeroExtend 64)
    (reubBase + 112) dstBytes di hdalign hdi hdover hdvalid
  rw [truncate_zeroExtend_byte] at sb
  have a5 := addi_spec_gen_same_within .x5 (srcBase + BitVec.ofNat 64 si) 1
    (reubBase + 116) (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega] at a5
  have a29 := addi_spec_gen_same_within .x29 (dstBase + BitVec.ofNat 64 di) 1
    (reubBase + 120) (by nofun)
  rw [show (dstBase + BitVec.ofNat 64 di) + signExtend12 (1 : BitVec 12)
      = dstBase + BitVec.ofNat 64 (di + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega] at a29
  have a6 := addi_spec_gen_same_within .x6 v6 (-1 : BitVec 12) (reubBase + 124) (by nofun)
  runBlock lbu sb a5 a29 a6

/-- `[32] JAL x0, -24` returns to the copy loop header.  Hoisted out of
    `reubCopyLoop`: inside that proof's `succ` branch the elaborator is already
    deep enough that this `bv_omega` on a concrete linked address overflows
    `maxRecDepth`. -/
private theorem reub_jal_back :
    (reubBase + 128) + signExtend21 (-24 : BitVec 21) = reubBase + 104 := by
  rw [show signExtend21 (-24 : BitVec 21) = -(24 : Word) from by decide]
  bv_omega

set_option maxRecDepth 8000 in
/-- **The payload copy loop** ([26]-[32]), `reubBase+104 → reubBase+132`, by
    induction on the counter: `n` bytes move from `src[si..]` to `dst[di..]`. -/
theorem reubCopyLoop (srcBase dstBase v30 : Word) (srcBytes dstBytes : List Byte)
    (si di n : Nat)
    (hsalign : srcBase.toNat % 8 = 0) (hdalign : dstBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length) (hdlen : di + n ≤ dstBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hdover : dstBase.toNat + (di + n) ≤ 2 ^ 64) (hn : n < 2 ^ 64)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true)
    (hdvalid : ∀ k, k < n → isValidByteAccess (dstBase + BitVec.ofNat 64 (di + k)) = true) :
    cpsTripleWithin (7 * n + 1) (reubBase + 104) (reubBase + 132) reubCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes)
      (((.x6 : Reg) ↦ᵣ (0 : Word)) **
       ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + n))) **
       regOwn .x30 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion srcBase srcBytes **
       bytesRegion dstBase (copyN dstBytes srcBytes di si n)) := by
  have ha_t : (reubBase + 104) + signExtend13 (28 : BitVec 13) = reubBase + 132 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (reubBase + 104 : Word) + 4 = reubBase + 108 := by bv_omega
  induction n generalizing si di dstBytes v30 with
  | zero =>
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0)
      (0 : Word) (reubBase + 104)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code (by reubmem 26) hbeq_framed
    have htaken := cpsBranchWithin_takenPath hbeq_ext (fun _ hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) htaken
    · xperm_hyp hp
    · rw [show (0#64 : Word) = 0 from by decide] at hq
      simp only [Nat.add_zero, copyN_zero]
      have hq1 := sepConj_mono_left
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 := sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_implies_regOwn .x30)))) h hq1
      xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x6 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (reubBase + 104)
    rw [ha_t, ha_f] at hbeq
    have hbeq_framed := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
       ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcBase srcBytes **
       bytesRegion dstBase dstBytes)
      (by pcFree) hbeq
    have hbeq_ext := cpsBranchWithin_extend_code (by reubmem 26) hbeq_framed
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) :=
      word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath hbeq_ext (fun _ hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hA1' : cpsTripleWithin 1 (reubBase + 104) (reubBase + 108) reubCode
        ((((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) **
          (((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
           ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
           ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcBase srcBytes **
           bytesRegion dstBase dstBytes))
        (((.x30 : Reg) ↦ᵣ v30) ** ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 di)) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (k + 1)) **
         bytesRegion srcBase srcBytes ** bytesRegion dstBase dstBytes **
         ((.x0 : Reg) ↦ᵣ (0 : Word))) :=
      cpsTripleWithin_weaken (fun _ hp => hp)
        (fun h hq => by
          have hq1 := sepConj_mono_left
            (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
          xperm_hyp hq1) hA1
    have hsi0 : si < srcBytes.length := by omega
    have hdi0 : di < dstBytes.length := by omega
    have body := reubCopyBody srcBase dstBase v30 (BitVec.ofNat 64 (k + 1))
      srcBytes dstBytes si di hsalign hdalign hsi0 hdi0 (by omega) (by omega)
      (hsvalid 0 (by omega)) (hdvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word)) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (reubBase + 128)
    rw [reub_jal_back] at hjal
    have hjal_ext := cpsTripleWithin_extend_code (by reubmem 32) hjal
    have hjal_S : cpsTripleWithin 1 (reubBase + 128) (reubBase + 104) reubCode
        (((.x30 : Reg) ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
         ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0)))
        (((.x30 : Reg) ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
         ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion srcBase srcBytes **
         bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0))) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          (((.x30 : Reg) ↦ᵣ (srcBytes[si]'hsi0).zeroExtend 64) **
           ((.x5 : Reg) ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           ((.x29 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 (di + 1))) **
           ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion srcBase srcBytes **
           bytesRegion dstBase (dstBytes.set di (srcBytes[si]'hsi0)))
          (by pcFree) hjal_ext)
    have hsvalid' : ∀ j, j < k →
        isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have hdvalid' : ∀ j, j < k →
        isValidByteAccess (dstBase + BitVec.ofNat 64 ((di + 1) + j)) = true := by
      intro j hj
      have h := hdvalid (j + 1) (by omega)
      rwa [show di + (j + 1) = (di + 1) + j from by omega] at h
    have ihspec := ih ((srcBytes[si]'hsi0).zeroExtend 64)
      (dstBytes.set di (srcBytes[si]'hsi0)) (si + 1) (di + 1)
      (by omega) (by rw [List.length_set]; omega) (by omega)
      (by rw [show (di + 1) + k = di + (k + 1) from by omega]; omega) (by omega)
      hsvalid' hdvalid'
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hA1' body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hbyte : (srcBytes[si]'hsi0) = getByteAt srcBytes si := by simp [getByteAt, hsi0]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega,
        show di + (k + 1) = (di + 1) + k from by omega,
        show copyN dstBytes srcBytes di si (k + 1)
           = copyN (dstBytes.set di (srcBytes[si]'hsi0)) srcBytes (di + 1) (si + 1) k from by
          rw [copyN_succ, ← hbyte]]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s1234

/-! ## §7  The header write ([21]-[25]) and the return tail ([33]-[34])

    `[21]`-`[23]` write the single header byte `0x80 + L` — which is why the
    routine's domain stops at `L ≤ 55`, since RLP switches to `0xb7 + lenlen`
    at 56 — and `[24]`/`[25]` set up the copy loop's destination cursor and
    counter.  `[33]`/`[34]` return `a0 = L + 1`. -/

/-- `[22] ADD x28, x28, x31` with `x28 = 0x80`.  Unconditional: `mod 2^64`
    absorbs the inner reduction, so no range side condition is needed. -/
private theorem word_128_add (L : Nat) :
    (128 : Word) + BitVec.ofNat 64 L = BitVec.ofNat 64 (128 + L) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (128 : Word).toNat = 128 from by decide]
  omega

/-- `[23] SB` stores the low byte of the header word.  Also unconditional, and
    deliberately says nothing about RLP validity: for `L ≥ 128` the byte wraps
    and the *encoding* is wrong, but this equation still holds.  The `L ≤ 55`
    domain restriction belongs to the model tie (`reubOut_short_form`), not
    here — putting it in this lemma would misplace it as an arithmetic fact. -/
private theorem truncate_header_byte (L : Nat) :
    (BitVec.ofNat 64 (128 + L)).truncate 8 = BitVec.ofNat 8 (128 + L) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- What the copy loop receives at `reubBase+104`: header byte written, source
    cursor at the payload, destination cursor one past the header. -/
def reubCopyPre (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n d : Nat)
    (v30 : Word) : Assertion :=
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
  ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
  ((.x29 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
  ((.x30 : Reg) ↦ᵣ v30) **
  ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (128 + (n - d))) **
  ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
  bytesRegion srcPtr xs **
  bytesRegion outPtr (oldOut.set 0 (BitVec.ofNat 8 (128 + (n - d)))) **
  ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
  ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word))

set_option maxRecDepth 8000 in
/-- **The header write** ([21]-[25]), `reubBase+84 → reubBase+104`. -/
theorem reubHeaderWrite (srcPtr outPtr raVal : Word) (xs oldOut : List Byte)
    (n d : Nat) (v29 v30 : Word)
    (holen : 0 < oldOut.length)
    (hoalign : outPtr.toNat % 8 = 0) (hoover : outPtr.toNat < 2 ^ 64)
    (hovalid : isValidByteAccess outPtr = true) :
    cpsTripleWithin 5 (reubBase + 84) (reubBase + 104) reubCode
      (reubHeaderPre srcPtr outPtr raVal xs oldOut n d v29 v30)
      (reubCopyPre srcPtr outPtr raVal xs oldOut n d v30) := by
  have haddr0 : outPtr + BitVec.ofNat 64 0 = outPtr := by bv_omega
  have hLI := li_spec_gen_within .x28 (1 : Word) (128 : Word) (reubBase + 84) (by decide)
  have hADD := add_spec_gen_rd_eq_rs1_within .x28 .x31 (128 : Word)
    (BitVec.ofNat 64 (n - d)) (reubBase + 88) (by decide)
  rw [word_128_add (n - d)] at hADD
  have hSB := bytesRegion_sb_within .x12 .x28 outPtr
    (BitVec.ofNat 64 (128 + (n - d))) (reubBase + 92) oldOut 0 hoalign holen
    (by omega) (by rw [haddr0]; exact hovalid)
  rw [haddr0, truncate_header_byte (n - d)] at hSB
  have hADDI := addi_spec_gen_within .x29 .x12 v29 outPtr (1 : BitVec 12)
    (reubBase + 96) (by decide)
  rw [show outPtr + signExtend12 (1 : BitVec 12) = outPtr + BitVec.ofNat 64 1 from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega] at hADDI
  have hMV := mv_spec_gen_within .x6 .x31 (BitVec.ofNat 64 (n - d))
    (BitVec.ofNat 64 (n - d)) (reubBase + 100) (by decide)
  unfold reubHeaderPre reubCopyPre reubAmb
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 5 (reubBase + 84) (reubBase + 104) reubCode
        (((.x28 : Reg) ↦ᵣ (1 : Word)) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x29 : Reg) ↦ᵣ v29) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         bytesRegion outPtr oldOut **
         ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcPtr xs **
         ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (128 + (n - d))) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x12 : Reg) ↦ᵣ outPtr) **
         ((.x29 : Reg) ↦ᵣ (outPtr + BitVec.ofNat 64 1)) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         bytesRegion outPtr (oldOut.set 0 (BitVec.ofNat 8 (128 + (n - d)))) **
         ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion srcPtr xs **
         ((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word))) from by
      (runBlock hLI hADD hSB hADDI hMV))
  · xperm_hyp hp
  · xperm_hyp hp

set_option maxRecDepth 8000 in
/-- **The return tail** ([33]-[34]), `reubBase+132 → ra &&& ~~~1`: the byte
    count is the payload plus its one header byte. -/
theorem reubRetTail (raVal v10 : Word) (L : Nat) :
    cpsTripleWithin 2 (reubBase + 132) (raVal &&& ~~~1) reubCode
      (((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 L) ** ((.x10 : Reg) ↦ᵣ v10) **
       ((.x1 : Reg) ↦ᵣ raVal))
      (((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 L) **
       ((.x10 : Reg) ↦ᵣ (BitVec.ofNat 64 L + (1 : Word))) **
       ((.x1 : Reg) ↦ᵣ raVal)) := by
  have hADDI := addi_spec_gen_within .x10 .x31 v10 (BitVec.ofNat 64 L)
    (1 : BitVec 12) (reubBase + 132) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hADDI
  have hRet := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (reubBase + 136)
  rw [show raVal + signExtend12 (0 : BitVec 12) = raVal from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega] at hRet
  runBlock hADDI hRet

/-! ## §8  The prologue ([0]-[1])

    `MV x5, a0` and `MV x6, a1` copy the ABI arguments into the strip loop's
    cursor and counter, which is exactly `reubInv … 0`: the cursor sits at
    offset zero and no leading zeros have been counted yet, so the invariant's
    bound is `0 ≤ reubZeros xs 0 n` — vacuous, and discharged by `Nat.zero_le`.

    `a1` stays live in `x11` afterwards (nothing reads or writes it again), so it
    is carried alongside the invariant rather than inside it. -/

set_option maxRecDepth 8000 in
/-- **The prologue** ([0]-[1]), `reubBase → reubBase+8`. -/
theorem reubPrologue (srcPtr outPtr raVal v5 v6 v28 : Word) (xs oldOut : List Byte)
    (n : Nat) :
    cpsTripleWithin 2 reubBase (reubBase + 8) reubCode
      (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x28 : Reg) ↦ᵣ v28) **
       bytesRegion srcPtr xs ** ((.x12 : Reg) ↦ᵣ outPtr) **
       ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion outPtr oldOut)
      (reubInv srcPtr outPtr raVal xs oldOut n 0 **
       ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n)) := by
  have hMV5 := mv_spec_gen_within .x5 .x10 srcPtr v5 reubBase (by decide)
  have hMV6 := mv_spec_gen_within .x6 .x11 (BitVec.ofNat 64 n) v6
    (reubBase + 4) (by decide)
  rw [show reubBase + 4 + 4 = reubBase + 8 from by bv_omega] at hMV6
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_)
    (show cpsTripleWithin 2 reubBase (reubBase + 8) reubCode
        (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x5 : Reg) ↦ᵣ v5) **
         ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** ((.x6 : Reg) ↦ᵣ v6) **
         ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcPtr xs **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut)
        (((.x10 : Reg) ↦ᵣ srcPtr) ** ((.x5 : Reg) ↦ᵣ srcPtr) **
         ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x28 : Reg) ↦ᵣ v28) ** bytesRegion srcPtr xs **
         ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut) from by
      (runBlock hMV5 hMV6))
  · xperm_hyp hp
  · -- `reubInv … 0` plus the still-live `a1`.  The pure bound is vacuous, but it
    -- cannot be introduced by `xperm` (adding a pure factor is not a heap
    -- permutation), so the `**` is split by hand and the left factor wrapped.
    unfold reubInv
    have hp3 := sepConj_mono (regIs_implies_regOwn .x28) (fun _ x => x) h
      (show (((.x28 : Reg) ↦ᵣ v28) **
          ((.x5 : Reg) ↦ᵣ srcPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ raVal) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion outPtr oldOut **
          ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n)) h from by xperm_hyp hp)
    have hsplit : (reubInvCore srcPtr outPtr raVal xs oldOut n 0 **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n)) h := by
      unfold reubInvCore reubStable reubAmb
      rw [show srcPtr + BitVec.ofNat 64 0 = srcPtr from by bv_omega, Nat.sub_zero]
      xperm_hyp hp3
    obtain ⟨h1, h2, hd, hu, hA, hB⟩ := hsplit
    exact ⟨h1, h2, hd, hu, (sepConj_pure_right h1).2 ⟨hA, Nat.zero_le _⟩, hB⟩

end RlpEncodeUintBeSAsm

end EvmAsm.Codegen
