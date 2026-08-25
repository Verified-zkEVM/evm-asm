/-
  EvmAsm.Codegen.Proofs.RlpContentStrictAtGuest

  **Image-anchored** whole-routine triples for the two canonical-strict RLP
  content decoders, GH #12799 ownership-table rows 1 and 2.

  ## What was missing, and what this module adds

  `EvmAsm/Rv64/RLP/ContentToU64Strict.lean` and `…/ContentToU256BeStrict.lean`
  already prove complete four-way whole-routine triples, but at a **free**
  `base`:

  ```
  cpsTripleWithin … base (raVal &&& ~~~1) (rlp_content_to_u64_strict_code base) …
  ```

  A position-independent triple is not the image claim — it says nothing about
  what the linked `stateless_guest` image holds at the routine's own address.
  `scripts/check-registry-coverage.py` graded both symbols `structured-only`,
  "position-independent base (base)", and their entries in
  `scripts/registry-coverage-allow.txt` named instantiation at
  `GuestAddrs.<sym>` as the remedy. This module performs that instantiation, so
  each contract is stated over

  ```
  CodeReq.ofProg GuestAddrs.rlp_content_to_u64_strict     rlp_content_to_u64_strict_prog
  CodeReq.ofProg GuestAddrs.rlp_content_to_u256_be_strict rlp_content_to_u256_be_strict_prog
  ```

  which is the abbrev `rlp_content_to_*_strict_code` unfolded at the linked
  entry address.

  ## Why these two, and why first

  Both are **leaf routines with zero callees and no stack frame** — no `sp`
  adjustment, no `ra` save — and both are the shared prerequisite of
  `header_extended_decode` (6 call sites of the u64 helper, 1 of the u256 one)
  and `header_extended_decode_arity_check` (1 each). 48 instructions buy the
  callee obligations of 291.

  ## The addresses, and how they were checked

  `GuestAddrs.rlp_content_to_u64_strict = 0x800053c0` and
  `GuestAddrs.rlp_content_to_u256_be_strict = 0x80005418`, both `LINK_DEPENDENT`
  rows of `scripts/asm-fixtures/symbol-addresses.tsv`. Disassembling the linked
  image at those addresses reproduces the two `_prog` definitions instruction
  for instruction (22/22 and 26/26), and the Lean side pins the same identity
  from the emission end: `rlpContentToU64StrictFunction_eq_verified_prog` and
  `rlpContentToU256BeStrictFunction_eq_verified_prog`
  (`EvmAsm/Codegen/Programs/RlpWalk.lean`) are `rfl`-checked, and the guest
  assembly for each symbol is `emitProgram` applied to exactly the `_prog` these
  triples run.

  ⚠️ **What is still NOT certified here.** Neither symbol has a
  `guestImageEntries` pairing, so `scripts/check-guest-image-program-bytes.py`
  does not cover them. That is not an oversight in this module: both bodies
  reach their program through the *qualified* name
  `EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog`, and
  `scripts/guest_image_coverage.py` refuses such a row outright, naming GH
  #12686 as an open design question (a plain-identifier alias satisfies that
  parser but not `check-asm-to-program.sh`'s drift guard, which wants a literal
  `def <prog> : Program := [...]` block in the manifest file). So the byte
  identity above rests on the `rfl`-checked emission identity plus a manual
  `objdump` read, not on the automated whole-guest gate. Registering the
  pairing is #12686's business, not this module's.

  ## Contents

  * `rlp_content_to_u64_strict_at_guest_spec_within` — row 1. All four exit
    paths (`len > 8` → `a1 = 2`; `len = 0` → `a0 = a1 = 0`; leading zero →
    `a1 = 3`; otherwise `a1 = 0`, `a0 = fromBytesBE content`).
  * `rlp_content_to_u256_be_strict_at_guest_spec_within` — row 2. All four exit
    paths (`len > 32` → `a0 = 2`; `len = 0` → `a0 = 0`, zero buffer; leading
    zero → `a0 = 3`; otherwise `a0 = 0`, right-aligned big-endian buffer).
    **Status is in `a0` here, not `a1`** — a different convention from the u64
    helper, read off `0x80005468`/`0x80005470`/`0x80005478` (`li a0,0` /
    `li a0,3` / `li a0,2`).
  * Four non-vacuity witnesses: a satisfiable instance for each triple whose
    live postcondition disjunct is the **accept** arm, and a negative control
    for each exhibiting an instantiation where the same conjuncts are provably
    **false**.

  Every clobbered register in each frame was read off the disassembly, not off
  the source: the u64 routine writes `a0 a1 t0 t1 t2 t3` (`x10 x11 x5 x6 x7
  x28`) and nothing else, and the u256 routine writes `a0 t0 t1 t2 t3 t4`
  (`x10 x5 x6 x7 x28 x29`) plus the 32 bytes at `a2`.
-/

import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.RLP.ContentToU64Strict
import EvmAsm.Rv64.RLP.ContentToU256BeStrict

namespace EvmAsm.Codegen.RlpContentStrictAtGuest

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.EL.RLP

/-! ## Extent pins

    The check that says the program *is* the routine, kernel-checked rather
    than asserted in prose. A symbol's extent is the **next symbol in address
    order** — not the next symbol matching a name filter, which is how three
    routines' code was once attributed to one symbol in #12799's own thread —
    and each `_prog` must exactly fill it.

    In `scripts/asm-fixtures/symbol-addresses.tsv` the address order around
    here is `rlp_content_to_u64` (`0x80005310`), `rlp_content_to_u256_be`
    (`0x80005358`), `rlp_content_to_u64_strict` (`0x800053c0`),
    `rlp_content_to_u256_be_strict` (`0x80005418`),
    `mpt_leaf_node_encode_from_nibbles` (`0x80005480`). So the two extents are
    88 and 104 bytes, i.e. 22 and 26 instructions, and the two `_prog`s have
    exactly those lengths. If a future layout change moves either symbol
    without moving the other, or if a `_prog` gains or loses an instruction,
    these fail rather than letting a row keep citing a contract about a
    different span. -/

theorem u64_strict_extent_pin :
    GuestAddrs.rlp_content_to_u64_strict + 4 * rlp_content_to_u64_strict_prog.length
      = GuestAddrs.rlp_content_to_u256_be_strict := by
  decide

theorem u256_be_strict_extent_pin :
    GuestAddrs.rlp_content_to_u256_be_strict + 4 * rlp_content_to_u256_be_strict_prog.length
      = GuestAddrs.mpt_leaf_node_encode_from_nibbles := by
  decide

/-! ## Row 1 — `rlp_content_to_u64_strict` @ `0x800053c0` (22 instructions) -/

/--
**Whole-routine triple for `rlp_content_to_u64_strict`, anchored at its linked
guest address.**

This is `EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_spec_within` instantiated at
`base := GuestAddrs.rlp_content_to_u64_strict`, so the `CodeReq` is
`CodeReq.ofProg GuestAddrs.rlp_content_to_u64_strict rlp_content_to_u64_strict_prog`
— the image claim, not a position-independent one.

**Exit paths — all four are covered**, matching the four `ret`s in the
disassembly:

| path | condition | `a0` | `a1` | `ret` at |
|---|---|---|---|---|
| too long | `8 < len` | `0` | `2` | `0x80005414` |
| empty-ok | `len = 0` | `0` | `0` | `0x80005400` |
| leading zero | `0 < len ≤ 8`, `content[0] = 0` | `0` | `3` | `0x80005408` |
| ok | `0 < len ≤ 8`, `content[0] ≠ 0` | `fromBytesBE content` | `0` | `0x80005400` |

Note the empty case is **accepted** with value `0`: the leading-zero reject at
`0x800053dc` is only reached after the `beqz t2` at `0x800053d4` has already
sent `len = 0` to the success return. Empty content is the canonical RLP zero
and the contract must not reject it.

**Frame, read off the listing at `0x800053c0..0x80005414`:**

* `x10`/`a0` (in: content pointer; out: value) — `mv t1,a0` @ `0x800053c8`
  consumes it, `li a0,0` @ `0x800053d0` and the `or` @ `0x800053ec` write it.
* `x11`/`a1` (in: length; out: status) — `mv t2,a1` @ `0x800053cc` consumes it;
  `li a1,{0,3,2}` @ `0x800053fc`/`0x80005404`/`0x80005410` write it.
* `x5`/`t0` — `li t0,8` @ `0x800053c0`. Returned as `regOwn`.
* `x6`/`t1` — cursor, `mv t1,a0` @ `0x800053c8`, `addi t1,t1,1` @ `0x800053f0`.
  Its incoming value is **arbitrary** (`x6Old`), because the routine's own `mv`
  overwrites it before first use. Returned as `regOwn`.
* `x7`/`t2` — remaining counter, `mv t2,a1` @ `0x800053cc`,
  `addi t2,t2,-1` @ `0x800053f4`. Returned as `regOwn`.
* `x28`/`t3` — loaded byte, `lbu t3,0(t1)` @ `0x800053d8`/`0x800053e8`.
  Returned as `regOwn`.
* `x1`/`ra` preserved (never written; the routine is a frameless leaf, so there
  is no `sd ra` and no `sp` adjustment anywhere in the 22 instructions).
* `x0` pinned to `0` as usual.
* No memory is written: `bytesRegion srcBase srcBytes` is returned unchanged.

Nothing else appears in the pre- or postcondition, because nothing else appears
in the listing.

**Loop.** The single loop is the back edge `j 0x800053e0` at `0x800053f8`; it is
proven by `cu64_strict_loop_spec_within`, which inducts on the remaining-length
counter held in `t2`/`x7` and decremented by `addi t2,t2,-1` at `0x800053f4`.
The whole-routine step bound `7 * len + 11` is the resulting static measure.
-/
theorem rlp_content_to_u64_strict_at_guest_spec_within
    (srcBase raVal t0Old x6Old t2Old t3Old : Word) (srcBytes : List (BitVec 8))
    (srcOff len : Nat)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) :
    cpsTripleWithin (7 * len + 11)
      (GuestAddrs.rlp_content_to_u64_strict : Word) (raVal &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.rlp_content_to_u64_strict : Word)
        rlp_content_to_u64_strict_prog)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ t2Old) **
       (.x28 ↦ᵣ t3Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes)
      ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (2 : Word)) ** ⌜8 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) ** ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (3 : Word)) **
            ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((srcBytes.drop srcOff).take len))) **
            (.x11 ↦ᵣ (0 : Word)) **
            ⌜0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) :=
  rlp_content_to_u64_strict_spec_within
    (GuestAddrs.rlp_content_to_u64_strict : Word) srcBase raVal t0Old x6Old t2Old t3Old
    srcBytes srcOff len hlen64 hsalign hslen hsover hsvalid

/-! ## Row 2 — `rlp_content_to_u256_be_strict` @ `0x80005418` (26 instructions) -/

/--
**Whole-routine triple for `rlp_content_to_u256_be_strict`, anchored at its
linked guest address.**

`EvmAsm.Rv64.RLP.rlp_content_to_u256_be_strict_spec_within` instantiated at
`base := GuestAddrs.rlp_content_to_u256_be_strict`, so the `CodeReq` is
`CodeReq.ofProg GuestAddrs.rlp_content_to_u256_be_strict
rlp_content_to_u256_be_strict_prog`.

⚠️ **The status register is `a0`, not `a1`.** The u64 helper one symbol back
returns its status in `a1`; this one returns it in `a0` and has no value
register at all (the result is the 32-byte buffer at `a2`). Read off
`li a0,0` @ `0x80005468`, `li a0,3` @ `0x80005470`, `li a0,2` @ `0x80005478`.

**Exit paths — all four are covered:**

| path | condition | `a0` | 32 bytes at `a2` | `ret` at |
|---|---|---|---|---|
| too long | `32 < len` | `2` | all zero | `0x8000547c` |
| empty-ok | `len = 0` | `0` | all zero | `0x8000546c` |
| leading zero | `0 < len`, `content[0] = 0` | `3` | all zero | `0x80005474` |
| ok | `0 < len ≤ 32`, `content[0] ≠ 0` | `0` | right-aligned BE | `0x8000546c` |

**The buffer is zeroed on every path, rejects included**, and the
postcondition says so on all four disjuncts. That is read off the four `sd
zero,…(a2)` at `0x80005418..0x80005424`, which run **before** the `bltu` length
check at `0x8000542c` and before the leading-zero test at `0x80005438`, so
neither reject path can escape them. A post that returned the buffer merely
*owned* on reject would be strictly weaker than the code, and one that dropped
it from the frame while the caller still owns the cell would be unsound; this
one pins the zeros.

Note again that `len = 0` is **accepted** (status `0`, buffer zero): the
`beqz a1` at `0x80005430` short-circuits to the success return before the
leading-zero test at `0x80005438` can fire.

**Frame, read off the listing at `0x80005418..0x8000547c`:**

* `x10`/`a0` (in: content pointer; out: status) — read by `lbu t1,0(a0)` @
  `0x80005434` and `mv t2,a0` @ `0x80005444`, written by the three `li a0,…`.
* `x11`/`a1` (in: length) — **preserved**; only read (`bltu`/`beqz`/`sub`/`mv`).
  The post returns it unchanged, which is what the disassembly supports: no
  instruction in the routine writes `a1`.
* `x12`/`a2` (in: output pointer) — **preserved**; the four `sd`s and the
  `add t1,a2,t0` @ `0x80005440` only read it.
* `x5`/`t0` — `li t0,32` @ `0x80005428`, `sub t0,t0,a1` @ `0x8000543c`.
  `regOwn`.
* `x6`/`t1` — the high byte at `0x80005434`, then the destination cursor
  `add t1,a2,t0` @ `0x80005440` / `addi t1,t1,1` @ `0x8000545c`. `regOwn`.
* `x7`/`t2` — source cursor, `mv t2,a0` @ `0x80005444`, `addi t2,t2,1` @
  `0x80005458`. `regOwn`.
* `x28`/`t3` — remaining counter, `mv t3,a1` @ `0x80005448`,
  `addi t3,t3,-1` @ `0x80005460`. `regOwn`.
* `x29`/`t4` — the copied byte, `lbu t4,0(t2)` @ `0x80005450`. `regOwn`.
* `x1`/`ra` preserved; frameless leaf, no `sp` traffic in the 26 instructions.
* Memory: the input `bytesRegion srcBase srcBytes` is returned unchanged; the
  32 bytes at `a2` are written on every path.

**Loop.** The single loop is the back edge `j 0x8000544c` at `0x80005464`,
proven by `cu256_strict_loop_spec_within` inducting on the remaining-length
counter in `t3`/`x28`, decremented by `addi t3,t3,-1` at `0x80005460`. Static
step bound `7 * len + 16`.
-/
theorem rlp_content_to_u256_be_strict_at_guest_spec_within
    (srcBase outPtr raVal x5Old x6Old x7Old x28Old x29Old : Word)
    (srcBytes : List (BitVec 8)) (srcOff len : Nat)
    (hlen64 : len < 2 ^ 64)
    (hsalign : srcBase.toNat % 8 = 0) (hoalign : outPtr.toNat % 8 = 0)
    (hslen : srcOff + len ≤ srcBytes.length)
    (hsover : srcBase.toNat + (srcOff + len) ≤ 2 ^ 64) (hoover : outPtr.toNat + 32 ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true)
    (hdvalid : ∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * len + 16)
      (GuestAddrs.rlp_content_to_u256_be_strict : Word) (raVal &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.rlp_content_to_u256_be_strict : Word)
        rlp_content_to_u256_be_strict_prog)
      ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
       (.x12 ↦ᵣ outPtr) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       (.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ x29Old) ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
       bytesRegion srcBase srcBytes ** memOwnU256Strict outPtr)
      (((.x11 ↦ᵣ BitVec.ofNat 64 len) ** (.x12 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
        bytesRegion srcBase srcBytes) **
       (fun h =>
         (((.x10 ↦ᵣ (2 : Word)) **
            bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) ** ⌜32 < len⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
            ⌜len = 0⌝) h) ∨
         (((.x10 ↦ᵣ (3 : Word)) **
            bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff = 0⌝) h) ∨
         (((.x10 ↦ᵣ (0 : Word)) **
            bytesRegion outPtr
              (copyNStrict (List.replicate 32 (0 : BitVec 8)) srcBytes (32 - len) srcOff len) **
            ⌜0 < len ∧ getByteAt srcBytes srcOff ≠ 0⌝) h))) :=
  rlp_content_to_u256_be_strict_spec_within
    (GuestAddrs.rlp_content_to_u256_be_strict : Word) srcBase outPtr raVal
    x5Old x6Old x7Old x28Old x29Old srcBytes srcOff len
    hlen64 hsalign hoalign hslen hsover hoover hsvalid hdvalid

/-! ## Non-vacuity: satisfiable instances and negative controls

    A contract nobody can instantiate proves nothing. Each triple above gets
    two witnesses:

    * an **instance** exhibiting concrete inputs that discharge every
      input-dependent hypothesis *and* land in the **accept** disjunct of the
      post (so the interesting arm is not vacuous either);
    * a **negative control** exhibiting an instantiation of the very same
      conjuncts that is provably **false**, so the hypotheses are known to
      exclude something rather than being trivially true.

    Both are registered in `EvmAsm/Progress/Routines.lean` so the axiom gate
    audits them, not just the triples. -/

/-- Concrete non-vacuity instance for
    `rlp_content_to_u64_strict_at_guest_spec_within`: content `[0x12, 0x34]` at
    the dword-aligned RAM address `0xa0001000`, offset `0`, length `2`. Every
    input-dependent hypothesis holds, and the trailing three conjuncts are
    exactly the guard of the post's **accept** disjunct
    (`0 < len ∧ len ≤ 8 ∧ content[0] ≠ 0`), so that arm is inhabited. -/
theorem rlp_content_to_u64_strict_at_guest_instance :
    ∃ (srcBase : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat),
      len < 2 ^ 64 ∧ srcBase.toNat % 8 = 0 ∧ srcOff + len ≤ srcBytes.length ∧
      srcBase.toNat + (srcOff + len) ≤ 2 ^ 64 ∧
      (∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) ∧
      0 < len ∧ len ≤ 8 ∧ getByteAt srcBytes srcOff ≠ 0 := by
  refine ⟨(0xa0001000 : Word), [(0x12 : BitVec 8), (0x34 : BitVec 8)], 0, 2,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Negative control for `rlp_content_to_u64_strict_at_guest_spec_within`.
    The routine's **own entry address** `0x800053c0` is dword-aligned, so the
    `hsalign` conjunct is satisfied there — and yet the `hsvalid` conjunct is
    provably false, because `.text` is outside every readable data window
    (`MEM 0x20..0x78000000`, `INPUT 0x40000000..0x40002000`,
    `RAM 0xa0000000..0xc0000000`). So the precondition bundle is a real
    restriction: it is not satisfied by every aligned address. -/
theorem rlp_content_to_u64_strict_at_guest_negative_control :
    ((GuestAddrs.rlp_content_to_u64_strict : Word).toNat % 8 = 0) ∧
    ¬ (∀ k, k < 2 →
        isValidByteAccess ((GuestAddrs.rlp_content_to_u64_strict : Word) +
          BitVec.ofNat 64 (0 + k)) = true) := by
  refine ⟨by decide, ?_⟩
  intro h
  have h0 := h 0 (by decide)
  revert h0
  decide

/-- Concrete non-vacuity instance for
    `rlp_content_to_u256_be_strict_at_guest_spec_within`: content `[0x12, 0x34]`
    at `0xa0001000`, output buffer at the disjoint dword-aligned RAM address
    `0xa0002000`, offset `0`, length `2`. Discharges every input-dependent
    hypothesis, including the 32 output-buffer validity obligations, and lands
    in the **accept** disjunct (`0 < len ∧ content[0] ≠ 0`). -/
theorem rlp_content_to_u256_be_strict_at_guest_instance :
    ∃ (srcBase outPtr : Word) (srcBytes : List (BitVec 8)) (srcOff len : Nat),
      len < 2 ^ 64 ∧ srcBase.toNat % 8 = 0 ∧ outPtr.toNat % 8 = 0 ∧
      srcOff + len ≤ srcBytes.length ∧
      srcBase.toNat + (srcOff + len) ≤ 2 ^ 64 ∧ outPtr.toNat + 32 ≤ 2 ^ 64 ∧
      (∀ k, k < len → isValidByteAccess (srcBase + BitVec.ofNat 64 (srcOff + k)) = true) ∧
      (∀ k, k < 32 → isValidByteAccess (outPtr + BitVec.ofNat 64 k) = true) ∧
      0 < len ∧ len ≤ 32 ∧ getByteAt srcBytes srcOff ≠ 0 := by
  refine ⟨(0xa0001000 : Word), (0xa0002000 : Word),
    [(0x12 : BitVec 8), (0x34 : BitVec 8)], 0, 2,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- Negative control for `rlp_content_to_u256_be_strict_at_guest_spec_within`,
    on the **output** side this time: `0xa0002004` is a perfectly valid byte
    address, so `hdvalid` holds there, and yet `hoalign` is provably false — the
    routine writes the buffer with `sd`, so a non-dword-aligned `a2` is outside
    the contract. Aligned-and-valid is a conjunction neither half implies. -/
theorem rlp_content_to_u256_be_strict_at_guest_negative_control :
    (∀ k, k < 32 → isValidByteAccess ((0xa0002004 : Word) + BitVec.ofNat 64 k) = true) ∧
    ¬ ((0xa0002004 : Word).toNat % 8 = 0) := by
  exact ⟨by decide, by decide⟩

end EvmAsm.Codegen.RlpContentStrictAtGuest
