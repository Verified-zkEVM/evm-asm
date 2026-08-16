/-
  EvmAsm.EL.RLP.RefDecode

  A name-for-name port of the reference RLP decoder — `ethereum_rlp.rlp` as
  vendored by the pinned `execution-specs` (e5a8caf1b, Amsterdam) — structured
  around the *same recursion* the reference uses:

    Ref.decode                 ← rlp.py `decode`
    Ref.decodeToBytes          ← rlp.py `decode_to_bytes`
    Ref.decodeToSequence       ← rlp.py `decode_to_sequence`
    Ref.decodeJoinedEncodings  ← rlp.py `decode_joined_encodings`
    Ref.decodeItemLength       ← rlp.py `decode_item_length`

  Unlike `EvmAsm.EL.RLP.decodeAux` (a fuel-indexed *streaming* decoder that
  returns leftover bytes), the reference decodes by *exact slicing*: a list
  header determines the payload window, `decode_item_length` determines each
  item's exact sub-window, and `decode` recurses on that exact slice, with
  every frame check ("truncated" / "trailing bytes") applied per window.
  This file mirrors that shape so that a machine implementation structured
  the same way has a spec whose recursion it can follow verbatim.

  Every reference `raise DecodingError` becomes `none`; since all failure
  modes collapse to `none`, only the accept set and the decoded value are
  observable, which is exactly the correspondence standard (iff).

  Two Python-int → Nat notes, both semantics-preserving on the reference's
  own behavior (not just on the dispatch domain):
  * `decode_to_bytes` computes `len_raw_data = b0 - 0x80`, which is negative
    for `b0 < 0x80` when the length-1 fast path did not fire, and then raises
    ("negative length").  Nat subtraction would silently truncate to 0, so the
    port makes the reject explicit (`if p < 0x80 then none`).
  * `decode_to_sequence`'s short arm computes `b0 - 0xC0`, negative for
    `b0 < 0xC0`; the reference then always raises via its trailing-bytes check
    (`1 + len_joined < len(encoded)` holds for any nonempty input when
    `len_joined < 0`).  The port rejects explicitly (`if p < 0xC0 then none`).
    `decode` only dispatches here for `b0 > 0xBF`, so the arm is off-domain
    anyway.

  ## Termination measure

  The reference recursion is `decode → decode_to_sequence → (loop:
  decode_joined_encodings) → decode` on exact sub-slices.  The named measure
  is `Ref.measure`:

      measure(decodeToSequence bs)      = 3 * bs.length
      measure(decode bs)                = 3 * bs.length + 1
      measure(decodeJoinedEncodings bs) = 3 * bs.length + 2

  Each call strictly decreases it:
  * `decode bs → decodeToSequence bs` — same window, phase 1 → 0;
  * `decodeToSequence bs → decodeJoinedEncodings payload` — the payload
    excludes at least the 1-byte header, `payload.length < bs.length`;
  * `decodeJoinedEncodings bs → decode (bs.take L)` — `L ≤ bs.length`,
    phase 2 → 1 (an item may span the whole remaining window);
  * `decodeJoinedEncodings bs → decodeJoinedEncodings (bs.drop L)` —
    `decodeItemLength` always returns `L ≥ 1` (`decodeItemLength_pos`).

  The equivalence with the streaming decoder actually used by SpecRef
  consumers (`Ref.decode bs = decodeFully bs`) is proved in
  `RefDecodeBridge.lean`.
-/

import EvmAsm.EL.RLP.Basic

namespace EvmAsm.EL.RLP.Ref

/-- Port of `decode_item_length` (rlp.py): the exact byte length of the RLP
    encoding of the first item in `bs`, from its header alone.  Performs only
    the header-level checks the reference performs here (length-of-length in
    range, first length byte nonzero); everything else is re-checked by the
    recursive `decode` on the exact slice. -/
def decodeItemLength (bs : List Byte) : Option Nat :=
  match bs with
  | [] => none
  | b0 :: rest =>
    let p := b0.toNat
    if p < 0x80 then
      some 1
    else if p ≤ 0xB7 then
      some (1 + (p - 0x80))
    else if p ≤ 0xBF then
      let lenLen := p - 0xB7
      if lenLen ≥ bs.length then none          -- "truncated"
      else if rest.getD 0 0 = (0 : Byte) then none
      else some (1 + lenLen + Nat.fromBytesBE (rest.take lenLen))
    else if p ≤ 0xF7 then
      some (1 + (p - 0xC0))
    else
      let lenLen := p - 0xF7
      if lenLen ≥ bs.length then none          -- "truncated"
      else if rest.getD 0 0 = (0 : Byte) then none
      else some (1 + lenLen + Nat.fromBytesBE (rest.take lenLen))

/-- `decode_item_length` never returns a length below 1 (a header is at least
    one byte).  This is what makes `decodeJoinedEncodings`' recursion on the
    remaining window well-founded. -/
theorem decodeItemLength_pos {bs : List Byte} {L : Nat}
    (h : decodeItemLength bs = some L) : 1 ≤ L := by
  cases bs with
  | nil => simp [decodeItemLength] at h
  | cons b0 rest =>
    simp only [decodeItemLength] at h
    repeat' split at h
    all_goals first
      | (injection h with h; omega)
      | injection h

/-- Port of `decode_to_bytes` (rlp.py): decode `bs` as a byte-string item,
    requiring the encoding to consume the window exactly. -/
def decodeToBytes (bs : List Byte) : Option (List Byte) :=
  match bs with
  | [] => none    -- unreachable from `decode` (which rejects empty input first)
  | b0 :: rest =>
    let p := b0.toNat
    if bs.length = 1 ∧ p < 0x80 then
      some bs
    else if p < 0x80 then
      none                                      -- "negative length"
    else if p ≤ 0xB7 then
      let lenRaw := p - 0x80
      if lenRaw ≥ bs.length then none           -- "truncated"
      else if 1 + lenRaw < bs.length then none  -- "trailing bytes"
      else
        let raw := rest.take lenRaw
        if lenRaw = 1 ∧ (raw.getD 0 0).toNat < 0x80 then none  -- non-canonical
        else some raw
    else
      let lenLen := p - 0xB7
      if lenLen ≥ bs.length then none           -- "truncated"
      else if rest.getD 0 0 = (0 : Byte) then none
      else
        let lenVal := Nat.fromBytesBE (rest.take lenLen)
        if lenVal < 0x38 then none              -- non-canonical long form
        else if lenLen + lenVal ≥ bs.length then none    -- "truncated"
        else if 1 + lenLen + lenVal < bs.length then none -- "trailing bytes"
        else some ((rest.drop lenLen).take lenVal)

mutual

/-- Port of `decode` (rlp.py): decode `bs` as one complete RLP item,
    consuming the window exactly. -/
def decode (bs : List Byte) : Option RLPItem :=
  match bs with
  | [] => none    -- "Cannot decode empty bytestring"
  | b0 :: tail =>
    if b0.toNat ≤ 0xBF then
      (decodeToBytes (b0 :: tail)).map .bytes
    else
      (decodeToSequence (b0 :: tail)).map .list
termination_by 3 * bs.length + 1
decreasing_by simp <;> omega

/-- Port of `decode_to_sequence` (rlp.py): decode `bs` as a list item —
    frame checks on the list header, then decode the exact payload window as
    joined encodings. -/
def decodeToSequence (bs : List Byte) : Option (List RLPItem) :=
  match bs with
  | [] => none    -- unreachable from `decode`
  | b0 :: rest =>
    let p := b0.toNat
    if p < 0xC0 then
      none                                      -- see header note (off-domain)
    else if p ≤ 0xF7 then
      let lenJoined := p - 0xC0
      if lenJoined ≥ bs.length then none        -- "truncated"
      else if 1 + lenJoined < bs.length then none -- "trailing bytes"
      else decodeJoinedEncodings (rest.take lenJoined)
      -- (payload excludes the header byte: `|rest.take _| ≤ |rest| < |bs|`)
    else
      let lenLen := p - 0xF7
      if lenLen ≥ bs.length then none           -- "truncated"
      else if rest.getD 0 0 = (0 : Byte) then none
      else
        let lenVal := Nat.fromBytesBE (rest.take lenLen)
        if lenVal < 0x38 then none              -- non-canonical long form
        else if lenLen + lenVal ≥ bs.length then none    -- "truncated"
        else if 1 + lenLen + lenVal < bs.length then none -- "trailing bytes"
        else decodeJoinedEncodings ((rest.drop lenLen).take lenVal)
termination_by 3 * bs.length
decreasing_by
  · simp [List.length_take] <;> omega
  · simp [List.length_take, List.length_drop] <;> omega

/-- Port of `decode_joined_encodings` (rlp.py): decode a concatenation of RLP
    encodings.  The reference iterates with a cursor; this port recurses on
    the remaining suffix, which is the same computation
    (`joined[cursor:]` ↦ `bs.drop L`). -/
def decodeJoinedEncodings (bs : List Byte) : Option (List RLPItem) :=
  match bs with
  | [] => some []
  | b0 :: tail =>
    match _hL : decodeItemLength (b0 :: tail) with
    | none => none
    | some L =>
      if L ≤ (b0 :: tail).length then
        -- reference: `start + L - 1 ≥ len` ⇒ "truncated"
        match decode ((b0 :: tail).take L) with
        | none => none
        | some item =>
          match decodeJoinedEncodings ((b0 :: tail).drop L) with
          | none => none
          | some items => some (item :: items)
      else none
termination_by 3 * bs.length + 2
decreasing_by
  · simp [List.length_take] <;> omega
  · have h1 := decodeItemLength_pos _hL
    simp [List.length_drop] <;> omega

end

/-! ## The depth-budgeted decoder

The reference (CPython) aborts on deep nesting with `RecursionError`
(measured on the pinned wheel at the default recursion limit: nesting depth
332 decodes, 333 raises — 3 interpreter frames per nesting level).  Per the
maintainer's ruling, an implementation must likewise *reject* deep nesting;
the bound doubles as the guest's constant-memory guarantee (stack per
nesting level × a constant).  `decodeD` is `decode` with the nesting bound
carried as an explicit parameter: the budget is spent once per list level,
and exhaustion rejects.  The machine routine implements `decodeD`; the cap
is a parameter of the program and of every theorem, never a literal. -/

mutual

/-- `decode` with a nesting budget: identical to `decode` except that a list
    header with zero remaining budget rejects.  One budget unit per list
    nesting level. -/
def decodeD (d : Nat) (bs : List Byte) : Option RLPItem :=
  match bs with
  | [] => none
  | b0 :: tail =>
    if b0.toNat ≤ 0xBF then
      (decodeToBytes (b0 :: tail)).map .bytes
    else
      match d with
      | 0 => none                    -- nesting budget exhausted: reject
      | d + 1 => (decodeToSequenceD d (b0 :: tail)).map .list
termination_by 3 * bs.length + 1
decreasing_by simp <;> omega

/-- Budgeted `decodeToSequence`: the payload's items decode at the given
    (already decremented) budget. -/
def decodeToSequenceD (d : Nat) (bs : List Byte) : Option (List RLPItem) :=
  match bs with
  | [] => none
  | b0 :: rest =>
    let p := b0.toNat
    if p < 0xC0 then
      none
    else if p ≤ 0xF7 then
      let lenJoined := p - 0xC0
      if lenJoined ≥ bs.length then none
      else if 1 + lenJoined < bs.length then none
      else decodeJoinedEncodingsD d (rest.take lenJoined)
    else
      let lenLen := p - 0xF7
      if lenLen ≥ bs.length then none
      else if rest.getD 0 0 = (0 : Byte) then none
      else
        let lenVal := Nat.fromBytesBE (rest.take lenLen)
        if lenVal < 0x38 then none
        else if lenLen + lenVal ≥ bs.length then none
        else if 1 + lenLen + lenVal < bs.length then none
        else decodeJoinedEncodingsD d ((rest.drop lenLen).take lenVal)
termination_by 3 * bs.length
decreasing_by
  · simp [List.length_take] <;> omega
  · simp [List.length_take, List.length_drop] <;> omega

/-- Budgeted `decodeJoinedEncodings`. -/
def decodeJoinedEncodingsD (d : Nat) (bs : List Byte) : Option (List RLPItem) :=
  match bs with
  | [] => some []
  | b0 :: tail =>
    match _hL : decodeItemLength (b0 :: tail) with
    | none => none
    | some L =>
      if L ≤ (b0 :: tail).length then
        match decodeD d ((b0 :: tail).take L) with
        | none => none
        | some item =>
          match decodeJoinedEncodingsD d ((b0 :: tail).drop L) with
          | none => none
          | some items => some (item :: items)
      else none
termination_by 3 * bs.length + 2
decreasing_by
  · simp [List.length_take] <;> omega
  · have h1 := decodeItemLength_pos _hL
    simp [List.length_drop] <;> omega

end

/-- Nesting depth of a decoded item: bytes cost nothing, each list level
    costs one budget unit. -/
def RLPItem.listDepth : RLPItem → Nat
  | .bytes _ => 0
  | .list items => 1 + (items.map RLPItem.listDepth).foldr max 0

#guard decodeD 0 [0x80#8] = some (.bytes [])
#guard decodeD 0 [0xc0#8] = none
#guard decodeD 1 [0xc0#8] = some (.list [])
#guard decodeD 1 [0xc1#8, 0xc0#8] = none
#guard decodeD 2 [0xc1#8, 0xc0#8] = some (.list [.list []])
#guard decodeD 2 [0xc2#8, 0xc0#8, 0x05#8] = some (.list [.list [], .bytes [0x05#8]])

/-! ## Pinned behavior vectors

Each `#guard` below mirrors an observation made by running the pinned
reference decoder itself (`execution-specs/.venv`, `ethereum_rlp.rlp.decode`)
on the same bytes — a direct, non-circular anchor of this port to the
reference, independent of any other Lean RLP code. -/

-- decode(b"") raises; single bytes below 0x80 are themselves
#guard decode [] = none
#guard decode [0x00#8] = some (.bytes [0x00#8])
#guard decode [0x7f#8] = some (.bytes [0x7f#8])
#guard decode [0x80#8] = some (.bytes [])
-- canonicity: a single byte < 0x80 must use the single-byte form
#guard decode [0x81#8, 0x00#8] = none
#guard decode [0x81#8, 0x7f#8] = none
#guard decode [0x81#8, 0x80#8] = some (.bytes [0x80#8])
-- exact consumption: trailing bytes rejected
#guard decode [0x80#8, 0x00#8] = none
#guard decode [0xc0#8, 0x00#8] = none
#guard decode [0xc1#8, 0x81#8, 0x00#8] = none
-- long-form boundary: 55 must be short, 56 must be long
#guard decode (0xb7#8 :: List.replicate 55 0x61#8)
  = some (.bytes (List.replicate 55 0x61#8))
#guard decode (0xb8#8 :: 0x37#8 :: List.replicate 55 0x61#8) = none
#guard decode (0xb8#8 :: 0x38#8 :: List.replicate 56 0x61#8)
  = some (.bytes (List.replicate 56 0x61#8))
#guard decode [0xb8#8, 0x00#8] = none
-- leading zero in a long length field
#guard decode (0xb9#8 :: 0x00#8 :: 0x38#8 :: List.replicate 56 0x61#8) = none
-- lists
#guard decode [0xc0#8] = some (.list [])
#guard decode [0xc1#8, 0x00#8] = some (.list [.bytes [0x00#8]])
#guard decode [0xc1#8, 0xc0#8] = some (.list [.list []])
#guard decode [0xc2#8, 0x81#8, 0x00#8] = none  -- inner non-canonical
#guard decode [0xc1#8, 0xbf#8] = none          -- inner header truncated
#guard decode (0xf7#8 :: List.replicate 55 0x80#8)
  = some (.list (List.replicate 55 (.bytes [])))
#guard decode (0xf8#8 :: 0x37#8 :: List.replicate 55 0x80#8) = none
#guard decode (0xf8#8 :: 0x38#8 :: List.replicate 56 0x80#8)
  = some (.list (List.replicate 56 (.bytes [])))
#guard decode [0xf8#8, 0x00#8] = none
#guard decode (0xbf#8 :: List.replicate 8 0x00#8) = none

end EvmAsm.EL.RLP.Ref
