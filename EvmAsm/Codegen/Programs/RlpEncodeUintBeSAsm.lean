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

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SAsm.MeasureLoop
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

/-- Strip-loop invariant after `j` rounds: cursor at `src+j`, counter `n-j`, and
    `j` bounded by the true leading-zero count. -/
def reubInv (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n j : Nat) :
    Assertion :=
  ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 j)) **
  ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - j)) **
  regOwn .x28 ** bytesRegion srcPtr xs **
  reubAmb srcPtr outPtr raVal oldOut **
  ⌜j ≤ reubZeros xs 0 n⌝

/-- The break post: the loop stopped at the first nonzero byte, whose offset is
    exactly the leading-zero count. -/
def reubBreakPost (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n : Nat) :
    Assertion :=
  fun h => ∃ d,
    (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
     ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
     regOwn .x28 ** bytesRegion srcPtr xs **
     reubAmb srcPtr outPtr raVal oldOut **
     ⌜d = reubZeros xs 0 n ∧ d < n⌝) h

/-- The exhaustion post: every byte was zero, so the stripped payload is empty
    and §3's tail is correct to write `0x80`. -/
def reubExhPost (srcPtr outPtr raVal : Word) (xs oldOut : List Byte) (n : Nat) :
    Assertion :=
  ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
  ((.x6 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x28 ** bytesRegion srcPtr xs **
  reubAmb srcPtr outPtr raVal oldOut **
  ⌜reubZeros xs 0 n = n⌝

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

end RlpEncodeUintBeSAsm

end EvmAsm.Codegen
