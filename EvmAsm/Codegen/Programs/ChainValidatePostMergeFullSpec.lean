/-
  EvmAsm.Codegen.Programs.ChainValidatePostMergeFullSpec

  **Whole-routine contract work for `chain_validate_post_merge_full` (GH #11576).**

  `docs/leaf-routine-targets.md` singles this routine out: it is the one member of the
  header family with NO whole-routine triple — `Programs/ChainValidatePostMerge.lean`
  carries only the string↔`Program` byte-identity theorem (`:608`).  The `Program`
  (`chainValidatePostMergeFull_prog`, `:422`, 149 instructions) exists, so a triple is
  attachable; this module attaches what is reachable in one file and names the rest.

  ## 1. The rule set, read off the BODY (not from memory)

  Instruction indices are into `chainValidatePostMergeFull_prog`; byte offsets are
  `4 * idx` from `D = ChainValidateOfflineAddrs.chain_validate_post_merge_full`.

  | idx | bytes | what the body does |
  |---|---|---|
  | 0–16 | `D..D+64` | prologue: frame `-56`, save `ra,s0,s1,s2,s3,s4,s5`; `s0:=N`, `s1:=lenBase`, `s2:=hdrBase`, `s3:=validPtr`, `s4:=codePtr`; `*validPtr:=1`, `*codePtr:=0`; `s5 := 0` |
  | 17 | `D+68` | loop guard `beq s5, s0, D+556` (exhausted → all-valid exit) |
  | 18–23 | `D+72` | spill `s2`/`s5` to `cvpmf_iter_ptr` / `cvpmf_iter_i` |
  | 24–31 | `D+96` | `a1 := lengths[i]`, `a0 := s2`, **`a2 := 7`**, `a3 := cvpmf_field`, `jal rlp_field_to_u64` |
  | 32 | `D+128` | `bne a0, x0, D+536` — callee status ≠ 0 → propagate |
  | 33–36 | `D+132` | reload `cvpmf_field`; **`bne t1, x0, D+432`** — ⇒ **RULE 1: field 7 (`difficulty`) must be 0** |
  | 37–50 | `D+148` | reload `s2`/`s5`; `a1 := lengths[i]`, `a0 := s2`, **`a2 := 14`**, `a3 := cvpmf_field`, `jal rlp_field_to_u64` |
  | 51 | `D+204` | `bne a0, x0, D+536` — propagate |
  | 52–55 | `D+208` | reload `cvpmf_field`; **`bne t1, x0, D+456`** — ⇒ **RULE 2: field 14 (`nonce`) must be 0** |
  | 56–71 | `D+224` | reload `s2`/`s5`; `a1 := lengths[i]`, `a0 := s2`, **`a2 := 1`**, `a3 := cvpmf_offset`, `a4 := cvpmf_length`, `jal rlp_list_nth_item` |
  | 72 | `D+288` | `bne a0, x0, D+536` — propagate |
  | 73–77 | `D+292` | `t1 := *cvpmf_length`; `li t2, 32`; **`bne t1, t2, D+504`** — ⇒ **RULE 3a: field 1 (`ommers_hash`) length = 32** |
  | 78–89 | `D+312` | reload `s2`/`s5`, `t2 := s2 + *cvpmf_offset`, `t3 := cvpmf_empty_hash` |
  | 90–101 | `D+360` | four `ld`/`ld`/`bne` dword compares at `0,8,16,24` against the baked constant, each branching to `D+480` — ⇒ **RULE 3b: those 32 bytes equal `EMPTY_OMMER_HASH`** |
  | 102–107 | `D+408` | `s2 += lengths[i]`; `s5 += 1`; `j D+68` |
  | 108–113 | `D+432` | difficulty violation: `*codePtr := i<<2 ||| 1`, `*validPtr := 0`, `a0 := 0` |
  | 114–119 | `D+456` | nonce violation: `*codePtr := i<<2 ||| 2`, `*validPtr := 0`, `a0 := 0` |
  | 120–125 | `D+480` | ommers-hash violation: `*codePtr := i<<2 ||| 3`, `*validPtr := 0`, `a0 := 0` |
  | 126–133 | `D+504` | size-fail: `*codePtr := i<<2 ||| 3`, `a0 := 3` (note: `*validPtr` NOT cleared) |
  | 134–138 | `D+536` | propagate: `*codePtr := i` (UNSHIFTED), `a0` left holding the callee's status |
  | 139 | `D+556` | all-valid exit: `a0 := 0` |
  | 140–148 | `D+560` | epilogue: restore, `addi sp, sp, 56`, `ret` |

  **The expected triple matches, exactly.**  The three rules the issue names —
  `difficulty = 0`, `nonce = 0`, `ommers_hash = EMPTY_OMMER_HASH` — are the three the
  body checks, at header RLP field indices `7`, `14`, `1`.  Those indices agree with
  `SpecRef.mkHeaderFields` (`Stateless.lean:182-190`: `difficulty := getN 7`,
  `nonce := getB 14`, `ommersHash := getB 1`) and with the routine's own siblings
  (`chain_validate_blob_gas_used_multiple` uses `17`, `blob_gas_used`).  The body checks
  no fourth rule, and omits none of the three.

  ### Four things the body does that the docstring at `ChainValidatePostMerge.lean:389`
  ### does not say, recorded because a caller could be misled by any of them

  1. **Neither `a0 = 1` nor `a0 = 2` is minted by this routine.**  The header comment
     lists `1 : RLP parse failure` and `2 : difficulty or nonce field > 8 bytes BE`, but
     the only `a0` writes in the whole `Program` are `li a0, 0` (idx 112, 118, 124,
     139), `li a0, 3` (idx 132), and `mv a0, s2` (idx 27, 46, 65, the argument setup).
     Both `1` and `2` reach the caller only through the propagate arm (`D+536`), which
     writes no `a0` at all and returns whatever `rlp_field_to_u64` /
     `rlp_list_nth_item` left there.  They are the *callee's* statuses, propagated —
     real values, but not codes this routine mints.
  2. **The size-fail arm leaves `*validPtr = 1`.**  `D+504..D+532` writes `*codePtr` and
     `a0 := 3` but never `sd zero, 0(s3)`.  A caller that reads `*validPtr` without
     first checking `a0` sees `1` on a header whose `ommers_hash` field is not 32 bytes.
     (`chain_validate_ommers_hash_empty`'s `.Lcvohe_size_fail` has the same shape, so
     this is the family convention `a0 ≠ 0 ⇒ *validPtr is meaningless`, not a fork.)
  3. **The propagate arm writes `*codePtr := i`, unshifted**, where every other failing
     arm writes `i<<2 ||| kind`.  Again disambiguated only by `a0 ≠ 0`.
  4. **The two numeric-looking call sites have different field types.**  Difficulty
     (field 7, idx 31) calls the strict `rlp_field_to_u64_strict` helper, while
     nonce (field 14, idx 50) calls lenient `rlp_field_to_u64`: nonce is fixed-width
     `Bytes8`, so leading zero bytes are data rather than scalar canonicality.
     The latter site was an unclassified field-14 check, distinct from the separate
     `chainValidateNonceZeroFunction`; it must not be swept along with difficulty.

  ## 2. `EMPTY_OMMER_HASH` — a drift gate, not a proof

  `SpecRef.EMPTY_OMMER_HASH` (`SeamShell.lean:111`) is `keccak256 (encS (.list []))`.
  ⚠️ `decide` on `keccak256` exhausts the recursion limit; this is measured and settled
  (see the docstring of `Programs/AccountDecodeCorrespondence.lean`, which pins the
  account sentinels the same way).  So the baked literal is pinned to a *written
  numeral* and to the four little-endian dwords the four `ld`/`bne` pairs actually
  compare (`cvpmfEmptyOmmerHash_dword{0,1,2,3}`), and the tie to `keccak256` is left as
  the named residual `EmptyOmmerHashPinned`.  That is a drift gate — it catches a typo in
  the 32 literal bytes — and explicitly NOT a proof that the literal is a keccak digest.

  ## 3. What this module proves, and what it does not

  Proven here, all kernel-checked (`#print axioms` shows only the three classical axioms):

  * `cvpmfPrologue` / `cvpmfEpilogue` — the two ends of the frame;
  * `cvpmfRetAllValid`, `cvpmfRetDifficulty`, `cvpmfRetNonce`, `cvpmfRetOmmers`,
    `cvpmfRetSizeFail`, `cvpmfRetPropagate` — **all six exit paths**, each from its own
    entry through the shared epilogue to `ra`, with the exact `*validPtr` / `*codePtr` /
    `a0` each one writes (so items 1–3 above are pinned in Lean, not only in prose);
  * `chain_validate_post_merge_full_spec_within_empty` — a **whole-routine**
    `cpsTripleWithin` from `D` to `ra`, DOMAIN-RESTRICTED to `N = 0`, whose post carries
    the (vacuous at `N = 0`) `∀`-over-headers verdict `PostMergeHeaderOk`.

  NOT proven here — the loop body (`D+68 → D+432/456/480/504/536` and back to `D+68`)
  for `N ≥ 1`.  Closing it needs the two callee contracts `rlpFieldToU64_spec_within`
  and `rlpListNthItem_spec_within` threaded through *three* calls plus a four-dword
  region compare; in the one-call siblings that is a 1200-line `…Loop.lean` plus a
  1100-line `…LoopClose.lean`, which does not fit the one-file budget of this issue.
  The domain restriction is written into the statement (`hN : lengths = []`), not into
  prose, and the missing obligation is named as `PostMergeLoopClosed`.
-/

import EvmAsm.Codegen.Programs.ChainValidatePostMerge
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.ChainValidateExtraDataLengthSpec
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Stateless.SpecRef.SeamShell
import EvmAsm.Stateless.SpecRef.Stateless
import EvmAsm.Codegen.Programs.ChainValidateOfflineAddrs

namespace EvmAsm.Codegen.ChainValidatePostMergeFullSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

local macro "pcfx" : tactic =>
  `(tactic| repeat' first
      | apply pcFree_sepConj | exact pcFree_regIs | exact pcFree_regOwn
      | exact pcFree_memIs | exact pcFree_memOwn | exact pcFree_emp | exact pcFree_pure
      | exact bytesRegion_pcFree _ _ | assumption)

/-! ## Base address, program, code -/

/-- The routine's guest base address. -/
abbrev D : Word := (ChainValidateOfflineAddrs.chain_validate_post_merge_full : Word)

/-- The routine's own `Program` (the one tied to the emitted string by
    `chainValidatePostMergeFullFunction_eq_prog`). -/
abbrev cvpmfProg : Program := EvmAsm.Codegen.chainValidatePostMergeFull_prog

set_option maxRecDepth 8000 in
theorem cvpmf_length : cvpmfProg.length = 149 := by decide

/-- The routine's instructions at its guest base. -/
def cvpmfCode : CodeReq := CodeReq.ofProg D cvpmfProg

/-! ## Scratch cells (`.data`, `ziskChainValidatePostMergeFullDataSection`) -/

abbrev Field : Word := (GuestAddrs.cvpmf_field : Word)
abbrev Off : Word := (GuestAddrs.cvpmf_offset : Word)
abbrev Len : Word := (GuestAddrs.cvpmf_length : Word)
abbrev IterPtr : Word := (GuestAddrs.cvpmf_iter_ptr : Word)
abbrev IterI : Word := (GuestAddrs.cvpmf_iter_i : Word)
abbrev EmptyHash : Word := (GuestAddrs.cvpmf_empty_hash : Word)

/-! ## The `EMPTY_OMMER_HASH` drift gate

    The 32 bytes baked at `cvpmf_empty_hash` by
    `ziskChainValidatePostMergeFullDataSection`, mirrored into Lean, pinned to a
    written numeral and to the four little-endian dwords the routine's four
    `ld`/`ld`/`bne` triples actually compare.  ⚠️ None of this evaluates `keccak256`;
    see `EmptyOmmerHashPinned` for the residual that would. -/

/-- The 32 literal bytes of the `.data` section, big-endian hash order. -/
def cvpmfEmptyOmmerHashBytes : List (BitVec 8) :=
  [0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a,
   0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a,
   0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13,
   0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47]

theorem cvpmfEmptyOmmerHashBytes_length : cvpmfEmptyOmmerHashBytes.length = 32 := by decide

/-- Drift gate (value): the baked bytes are the written numeral
    `0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347`. -/
theorem cvpmfEmptyOmmerHashBytes_value :
    EvmAsm.EL.RLP.Nat.fromBytesBE cvpmfEmptyOmmerHashBytes =
      0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347 := by
  decide

/-- Drift gate (machine form), dword 0: the first `ld` at `cvpmf_empty_hash + 0`. -/
theorem cvpmfEmptyOmmerHash_dword0 :
    packBytes (cvpmfEmptyOmmerHashBytes.take 8) = (0x7a5dc7dee84dcc1d : Word) := by decide

/-- Drift gate (machine form), dword 1: the `ld` at `cvpmf_empty_hash + 8`. -/
theorem cvpmfEmptyOmmerHash_dword1 :
    packBytes ((cvpmfEmptyOmmerHashBytes.drop 8).take 8) = (0x1ad4ccb667b585ab : Word) := by
  decide

/-- Drift gate (machine form), dword 2: the `ld` at `cvpmf_empty_hash + 16`. -/
theorem cvpmfEmptyOmmerHash_dword2 :
    packBytes ((cvpmfEmptyOmmerHashBytes.drop 16).take 8) = (0x13748a941b4512d3 : Word) := by
  decide

/-- Drift gate (machine form), dword 3: the `ld` at `cvpmf_empty_hash + 24`. -/
theorem cvpmfEmptyOmmerHash_dword3 :
    packBytes ((cvpmfEmptyOmmerHashBytes.drop 24).take 8) = (0x4793d440fd42a1f0 : Word) := by
  decide

/-! ## The SpecRef-side rule set

    `validate_header` (`SpecRef/SeamShell.lean:232`) checks, among other clauses,
    exactly the three EIP-3675 conjuncts at `:250`, `:251`, `:253` — and
    `_payload_header` (`:123`) constructs them.  Those three, and only those three, are
    what this routine tests. -/

open EvmAsm.Stateless.SpecRef in
/-- The three post-merge clauses of `validate_header`, as a predicate on one
    RLP-encoded header.  `difficulty` is `getN 7`, `nonce` is `getB 14`, `ommersHash`
    is `getB 1` — the same three fields, at the same three indices, that the body reads. -/
def PostMergeHeaderOk (encoded : Bytes) : Prop :=
  ∃ h : Header, _decode_header encoded = .ok h ∧
    h.difficulty = 0 ∧
    h.nonce = List.replicate 8 (0 : Byte) ∧
    h.ommersHash = EMPTY_OMMER_HASH

/-! ### The nonce clause: the guest's `u64 = 0` test versus the port's byte-list test

    The body tests `rlp_field_to_u64(field 14) = 0`; the port tests
    `nonce = List.replicate 8 0x00`.  These coincide exactly when the field is 8 bytes
    wide — which `_decode_header` enforces (`fixedBytesFieldWidths` carries `(14, 8)`),
    but which the *guest* does not itself check.  The bridge is proven here rather than
    assumed, so the leniency question is settled instead of left open. -/

/-- A big-endian byte string decodes to `0` exactly when every byte is `0`. -/
theorem fromBytesBE_eq_zero_iff (bs : List EvmAsm.EL.RLP.Byte) :
    EvmAsm.EL.RLP.Nat.fromBytesBE bs = 0 ↔ bs = List.replicate bs.length 0 := by
  induction bs with
  | nil => simp [EvmAsm.EL.RLP.Nat.fromBytesBE]
  | cons b bs ih =>
      rw [EvmAsm.EL.RLP.Nat.fromBytesBE, List.length_cons, List.replicate_succ,
        List.cons.injEq]
      have hpow : (256 : Nat) ^ bs.length ≠ 0 := by positivity
      constructor
      · intro h
        have hsplit := Nat.eq_zero_of_add_eq_zero_right h
        have hrest := Nat.eq_zero_of_add_eq_zero_left h
        refine ⟨?_, ih.mp hrest⟩
        have hb : b.toNat = 0 := by
          rcases Nat.mul_eq_zero.mp hsplit with hb | hp
          · exact hb
          · exact absurd hp hpow
        exact BitVec.eq_of_toNat_eq (by simpa using hb)
      · rintro ⟨hb, hrest⟩
        subst hb
        rw [ih.mpr hrest]
        simp

/-- **The nonce-rule bridge.**  On an 8-byte field the guest's `u64 = 0` test is
    literally the port's `nonce = replicate 8 0x00` test. -/
theorem nonce_rule_agrees (bs : List EvmAsm.EL.RLP.Byte) (hlen : bs.length = 8) :
    EvmAsm.EL.RLP.Nat.fromBytesBE bs = 0 ↔ bs = List.replicate 8 (0 : EvmAsm.EL.RLP.Byte) := by
  rw [fromBytesBE_eq_zero_iff, hlen]

/-! ## Prologue (idx 0–16, `D → D+68`)

    Byte-identical to the `chain_validate_extra_data_length` /
    `chain_validate_blob_gas_used_multiple` prologues. -/

set_option maxRecDepth 8000 in
theorem cvpmfPrologue
    (sp0 spC nWord lenBase hdrBase validPtr codePtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12)) :
    cpsTripleWithin 17 D (D + 68) cvpmfCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) **
        (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ codePtr) ** (.x5 ↦ᵣ old5) **
        (.x0 ↦ᵣ (0 : Word)) **
        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
        memOwn (spC + 32) ** memOwn (spC + 40) ** memOwn (spC + 48) **
        memOwn validPtr ** memOwn codePtr)
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ nWord) ** (.x9 ↦ᵣ lenBase) **
        (.x18 ↦ᵣ hdrBase) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ codePtr) **
        (.x21 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) **
        (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ codePtr) **
        (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5) ** (validPtr ↦ₘ (1 : Word)) **
        (codePtr ↦ₘ (0 : Word))) := by
  subst hspC
  have h0 := addi_spec_gen_same_within .x2 sp0 (-56 : BitVec 12) D (by decide)
  have h1 := sd_spec_gen_own_within .x2 .x1
    (sp0 + signExtend12 (-56 : BitVec 12)) raIn (0 : BitVec 12) (D + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at h1
  have h2 := sd_spec_gen_own_within .x2 .x8
    (sp0 + signExtend12 (-56 : BitVec 12)) cs0 (8 : BitVec 12) (D + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at h2
  have h3 := sd_spec_gen_own_within .x2 .x9
    (sp0 + signExtend12 (-56 : BitVec 12)) cs1 (16 : BitVec 12) (D + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at h3
  have h4 := sd_spec_gen_own_within .x2 .x18
    (sp0 + signExtend12 (-56 : BitVec 12)) cs2 (24 : BitVec 12) (D + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at h4
  have h5 := sd_spec_gen_own_within .x2 .x19
    (sp0 + signExtend12 (-56 : BitVec 12)) cs3 (32 : BitVec 12) (D + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at h5
  have h6 := sd_spec_gen_own_within .x2 .x20
    (sp0 + signExtend12 (-56 : BitVec 12)) cs4 (40 : BitVec 12) (D + 24)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at h6
  have h7 := sd_spec_gen_own_within .x2 .x21
    (sp0 + signExtend12 (-56 : BitVec 12)) cs5 (48 : BitVec 12) (D + 28)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at h7
  have h8 := mv_spec_gen_within .x8 .x10 nWord cs0 (D + 32) (by decide)
  have h9 := mv_spec_gen_within .x9 .x11 lenBase cs1 (D + 36) (by decide)
  have h10 := mv_spec_gen_within .x18 .x12 hdrBase cs2 (D + 40) (by decide)
  have h11 := mv_spec_gen_within .x19 .x13 validPtr cs3 (D + 44) (by decide)
  have h12 := mv_spec_gen_within .x20 .x14 codePtr cs4 (D + 48) (by decide)
  have h13 := li_spec_gen_within .x5 old5 (1 : Word) (D + 52) (by decide)
  have h14 := sd_spec_gen_own_within .x19 .x5 validPtr (1 : Word) (0 : BitVec 12) (D + 56)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at h14
  have h15 := sd_spec_gen_own_within .x20 .x0 codePtr (0 : Word) (0 : BitVec 12) (D + 60)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show codePtr + (0 : Word) = codePtr from by bv_omega] at h15
  have h16 := li_spec_gen_within .x21 cs5 (0 : Word) (D + 64) (by decide)
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

/-! ## Epilogue (idx 140–148, `D+560 → ra`) -/

set_option maxRecDepth 8000 in
theorem cvpmfEpilogue
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 9 (D + 560) raIn cvpmfCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5)) := by
  subst hspC
  have l0 := ld_spec_gen_within .x1 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o1 raIn
    (0 : BitVec 12) (D + 560) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-56 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-56 : BitVec 12) from by bv_omega] at l0
  have l1 := ld_spec_gen_within .x8 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o8 cs0
    (8 : BitVec 12) (D + 564) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at l1
  have l2 := ld_spec_gen_within .x9 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o9 cs1
    (16 : BitVec 12) (D + 568) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at l2
  have l3 := ld_spec_gen_within .x18 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o18 cs2
    (24 : BitVec 12) (D + 572) (by decide)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at l3
  have l4 := ld_spec_gen_within .x19 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o19 cs3
    (32 : BitVec 12) (D + 576) (by decide)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at l4
  have l5 := ld_spec_gen_within .x20 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o20 cs4
    (40 : BitVec 12) (D + 580) (by decide)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at l5
  have l6 := ld_spec_gen_within .x21 .x2 (sp0 + signExtend12 (-56 : BitVec 12)) o21 cs5
    (48 : BitVec 12) (D + 584) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at l6
  have l7 := addi_spec_gen_same_within .x2 (sp0 + signExtend12 (-56 : BitVec 12))
    (56 : BitVec 12) (D + 588) (by decide)
  rw [show (sp0 + signExtend12 (-56 : BitVec 12)) + signExtend12 (56 : BitVec 12) = sp0
      from by rw [show signExtend12 (-56 : BitVec 12) = (-56 : Word) from by decide,
        show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]; bv_omega] at l7
  have hblock : cpsTripleWithin 8 (D + 560) (D + 592) cvpmfCode
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-56 : BitVec 12))) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) **
        (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) **
        (.x21 ↦ᵣ o21) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5))
      ((.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
        ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
        ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) := by
    runBlock l0 l1 l2 l3 l4 l5 l6 l7
  have hjalr := EvmAsm.Evm64.ret_spec_within' (D + 592) raIn
  rw [hret] at hjalr
  have hjalrC := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 592) cvpmfProg 148 (.JALR .x0 .x1 (0 : BitVec 12))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide))
    hjalr
  have hjalrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) **
      (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) ** (.x2 ↦ᵣ sp0) **
      ((sp0 + signExtend12 (-56 : BitVec 12)) ↦ₘ raIn) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 8) ↦ₘ cs0) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 16) ↦ₘ cs1) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 24) ↦ₘ cs2) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 32) ↦ₘ cs3) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 40) ↦ₘ cs4) **
      ((sp0 + signExtend12 (-56 : BitVec 12) + 48) ↦ₘ cs5)) (by pcf) hjalrC
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblock hjalrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Exit 1 — all valid (idx 139 → epilogue, `D+556 → ra`)

    `a0 := 0`; `*validPtr` and `*codePtr` keep their prologue values. -/

set_option maxRecDepth 8000 in
theorem cvpmfRetAllValid
    (sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5 : Word) (G : Assertion) (hG : G.pcFree)
    (o10 o1 o8 o9 o18 o19 o20 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 10 (D + 556) raIn cvpmfCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
        (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have h139 := li_spec_gen_within .x10 o10 (0 : Word) (D + 556) (by decide)
  have h139C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 556) cvpmfProg 139 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide))
    h139
  have h139F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (.x19 ↦ᵣ o19) ** (.x20 ↦ᵣ o20) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) (by pcfx) h139C
  have hepi := cvpmfEpilogue sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 o20 o21 hspC hret
  have hepiF := cpsTripleWithin_frameR ((.x10 ↦ᵣ (0 : Word)) ** G)
    (by refine pcFree_sepConj ?_ hG; pcf) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h139F hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Exits 2–4 — the three rule violations

    Identical shape at three addresses, differing only in the `ori` kind tag and the
    `jal` displacement back to the shared epilogue:

    | rule | entry | kind | `jal` |
    |---|---|---|---|
    | RULE 1 `difficulty ≠ 0` | `D+432` | `1` | `+108` |
    | RULE 2 `nonce ≠ 0`      | `D+456` | `2` | `+84`  |
    | RULE 3 `ommers_hash ≠ EMPTY_OMMER_HASH` | `D+480` | `3` | `+60` |

    Each writes `*validPtr := 0`, `*codePtr := (i <<< 2) ||| kind`, `a0 := 0`. -/

set_option maxRecDepth 8000 in
theorem cvpmfRetDifficulty
    (sp0 spC raIn iWord validPtr codePtr cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (G : Assertion) (hG : G.pcFree) (o7 o10 o1 o8 o9 o18 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 15 (D + 432) raIn cvpmfCode
      ((.x7 ↦ᵣ o7) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ codePtr) ** (.x21 ↦ᵣ iWord) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        memOwn validPtr ** memOwn codePtr **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (codePtr ↦ₘ ((iWord <<< 2) ||| (1 : Word))) **
        (.x7 ↦ᵣ ((iWord <<< 2) ||| (1 : Word))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have s0 := slli_spec_gen_within .x7 .x21 o7 iWord (2 : BitVec 6) (D + 432) (by decide)
  rw [show ((2 : BitVec 6).toNat) = 2 from by decide] at s0
  have s1 := ori_spec_gen_same_within .x7 (iWord <<< 2) (1 : BitVec 12) (D + 436) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at s1
  have s2 := sd_spec_gen_own_within .x19 .x0 validPtr (0 : Word) (0 : BitVec 12) (D + 440)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at s2
  have s3 := sd_spec_gen_own_within .x20 .x7 codePtr ((iWord <<< 2) ||| (1 : Word))
    (0 : BitVec 12) (D + 444)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show codePtr + (0 : Word) = codePtr from by bv_omega] at s3
  have s4 := li_spec_gen_within .x10 o10 (0 : Word) (D + 448) (by decide)
  have s5 := jal_x0_spec_gen_within
    (EvmAsm.Codegen.jalOff (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 452)) (D + 452)
  rw [show (D + 452) + signExtend21
      (EvmAsm.Codegen.jalOff (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
        (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 452)) = D + 560 from by
    -- D = ofNat base; reduce both sides to ofNat form via ofNat_add
    change BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 452 +
        signExtend21 (jalOff (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
          (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 452)) =
      BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 560
    have hL : BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 452 =
        BitVec.ofNat 64 (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 452) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : ChainValidateOfflineAddrs.chain_validate_post_merge_full + 452 < 2 ^ 64); omega
    have hR : BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 560 =
        BitVec.ofNat 64 (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560 < 2 ^ 64); omega
    rw [hL, hR]
    exact jalOff_correct (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 452) (by decide)] at s5
  have hblock : cpsTripleWithin 6 (D + 432) (D + 560) cvpmfCode
      ((.x21 ↦ᵣ iWord) ** (.x7 ↦ᵣ o7) ** (.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn validPtr ** (.x20 ↦ᵣ codePtr) ** memOwn codePtr ** (.x10 ↦ᵣ o10))
      ((.x21 ↦ᵣ iWord) ** (.x7 ↦ᵣ ((iWord <<< 2) ||| (1 : Word))) **
        (.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (.x20 ↦ᵣ codePtr) ** (codePtr ↦ₘ ((iWord <<< 2) ||| (1 : Word))) **
        (.x10 ↦ᵣ (0 : Word))) := by
    runBlock s0 s1 s2 s3 s4 s5
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) (by pcfx) hblock
  have hepi := cvpmfEpilogue sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 validPtr codePtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
      (codePtr ↦ₘ ((iWord <<< 2) ||| (1 : Word))) **
      (.x7 ↦ᵣ ((iWord <<< 2) ||| (1 : Word))) ** (.x0 ↦ᵣ (0 : Word)) ** G)
    (by pcfx) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
theorem cvpmfRetNonce
    (sp0 spC raIn iWord validPtr codePtr cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (G : Assertion) (hG : G.pcFree) (o7 o10 o1 o8 o9 o18 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 15 (D + 456) raIn cvpmfCode
      ((.x7 ↦ᵣ o7) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ codePtr) ** (.x21 ↦ᵣ iWord) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        memOwn validPtr ** memOwn codePtr **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (codePtr ↦ₘ ((iWord <<< 2) ||| (2 : Word))) **
        (.x7 ↦ᵣ ((iWord <<< 2) ||| (2 : Word))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have s0 := slli_spec_gen_within .x7 .x21 o7 iWord (2 : BitVec 6) (D + 456) (by decide)
  rw [show ((2 : BitVec 6).toNat) = 2 from by decide] at s0
  have s1 := ori_spec_gen_same_within .x7 (iWord <<< 2) (2 : BitVec 12) (D + 460) (by decide)
  rw [show signExtend12 (2 : BitVec 12) = (2 : Word) from by decide] at s1
  have s2 := sd_spec_gen_own_within .x19 .x0 validPtr (0 : Word) (0 : BitVec 12) (D + 464)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at s2
  have s3 := sd_spec_gen_own_within .x20 .x7 codePtr ((iWord <<< 2) ||| (2 : Word))
    (0 : BitVec 12) (D + 468)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show codePtr + (0 : Word) = codePtr from by bv_omega] at s3
  have s4 := li_spec_gen_within .x10 o10 (0 : Word) (D + 472) (by decide)
  have s5 := jal_x0_spec_gen_within
    (EvmAsm.Codegen.jalOff (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 476)) (D + 476)
  rw [show (D + 476) + signExtend21
      (EvmAsm.Codegen.jalOff (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
        (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 476)) = D + 560 from by
    change BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 476 +
        signExtend21 (jalOff (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
          (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 476)) =
      BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 560
    have hL : BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 476 =
        BitVec.ofNat 64 (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 476) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : ChainValidateOfflineAddrs.chain_validate_post_merge_full + 476 < 2 ^ 64); omega
    have hR : BitVec.ofNat 64 ChainValidateOfflineAddrs.chain_validate_post_merge_full + BitVec.ofNat 64 560 =
        BitVec.ofNat 64 (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (by decide : ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560 < 2 ^ 64); omega
    rw [hL, hR]
    exact jalOff_correct (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 560)
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 476) (by decide)] at s5
  have hblock : cpsTripleWithin 6 (D + 456) (D + 560) cvpmfCode
      ((.x21 ↦ᵣ iWord) ** (.x7 ↦ᵣ o7) ** (.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn validPtr ** (.x20 ↦ᵣ codePtr) ** memOwn codePtr ** (.x10 ↦ᵣ o10))
      ((.x21 ↦ᵣ iWord) ** (.x7 ↦ᵣ ((iWord <<< 2) ||| (2 : Word))) **
        (.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (.x20 ↦ᵣ codePtr) ** (codePtr ↦ₘ ((iWord <<< 2) ||| (2 : Word))) **
        (.x10 ↦ᵣ (0 : Word))) := by
    runBlock s0 s1 s2 s3 s4 s5
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) (by pcfx) hblock
  have hepi := cvpmfEpilogue sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 validPtr codePtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
      (codePtr ↦ₘ ((iWord <<< 2) ||| (2 : Word))) **
      (.x7 ↦ᵣ ((iWord <<< 2) ||| (2 : Word))) ** (.x0 ↦ᵣ (0 : Word)) ** G)
    (by pcfx) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
theorem cvpmfRetOmmers
    (sp0 spC raIn iWord validPtr codePtr cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (G : Assertion) (hG : G.pcFree) (o7 o10 o1 o8 o9 o18 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 15 (D + 480) raIn cvpmfCode
      ((.x7 ↦ᵣ o7) ** (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ codePtr) ** (.x21 ↦ᵣ iWord) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
        memOwn validPtr ** memOwn codePtr **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (codePtr ↦ₘ ((iWord <<< 2) ||| (3 : Word))) **
        (.x7 ↦ᵣ ((iWord <<< 2) ||| (3 : Word))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have s0 := slli_spec_gen_within .x7 .x21 o7 iWord (2 : BitVec 6) (D + 480) (by decide)
  rw [show ((2 : BitVec 6).toNat) = 2 from by decide] at s0
  have s1 := ori_spec_gen_same_within .x7 (iWord <<< 2) (3 : BitVec 12) (D + 484) (by decide)
  rw [show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide] at s1
  have s2 := sd_spec_gen_own_within .x19 .x0 validPtr (0 : Word) (0 : BitVec 12) (D + 488)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show validPtr + (0 : Word) = validPtr from by bv_omega] at s2
  have s3 := sd_spec_gen_own_within .x20 .x7 codePtr ((iWord <<< 2) ||| (3 : Word))
    (0 : BitVec 12) (D + 492)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show codePtr + (0 : Word) = codePtr from by bv_omega] at s3
  have s4 := li_spec_gen_within .x10 o10 (0 : Word) (D + 496) (by decide)
  have s5 := jal_x0_spec_gen_within (60 : BitVec 21) (D + 500)
  rw [show (D + 500) + signExtend21 (60 : BitVec 21) = D + 560 from by
    rw [show signExtend21 (60 : BitVec 21) = (60 : Word) from by decide]; bv_omega] at s5
  have hblock : cpsTripleWithin 6 (D + 480) (D + 560) cvpmfCode
      ((.x21 ↦ᵣ iWord) ** (.x7 ↦ᵣ o7) ** (.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn validPtr ** (.x20 ↦ᵣ codePtr) ** memOwn codePtr ** (.x10 ↦ᵣ o10))
      ((.x21 ↦ᵣ iWord) ** (.x7 ↦ᵣ ((iWord <<< 2) ||| (3 : Word))) **
        (.x19 ↦ᵣ validPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
        (.x20 ↦ᵣ codePtr) ** (codePtr ↦ₘ ((iWord <<< 2) ||| (3 : Word))) **
        (.x10 ↦ᵣ (0 : Word))) := by
    runBlock s0 s1 s2 s3 s4 s5
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) (by pcfx) hblock
  have hepi := cvpmfEpilogue sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 validPtr codePtr iWord hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (0 : Word)) **
      (codePtr ↦ₘ ((iWord <<< 2) ||| (3 : Word))) **
      (.x7 ↦ᵣ ((iWord <<< 2) ||| (3 : Word))) ** (.x0 ↦ᵣ (0 : Word)) ** G)
    (by pcfx) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Exit 5 — `ommers_hash` field width ≠ 32 (idx 126–133, `D+504 → ra`)

    ⚠️ This arm writes `a0 := 3` and `*codePtr := i<<2 ||| 3` but **leaves `*validPtr`
    untouched** — `validPtr` appears in neither the pre nor the post below, i.e. it is
    outside this arm's footprint entirely.  That is the Lean-level statement of
    discrepancy 2 in this module's header: whatever the prologue put there (`1`)
    survives to the caller alongside `a0 = 3`. -/

set_option maxRecDepth 8000 in
theorem cvpmfRetSizeFail
    (sp0 spC raIn iWord codePtr cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (G : Assertion) (hG : G.pcFree) (o5 o6 o7 o10 o1 o8 o9 o18 o19 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 17 (D + 504) raIn cvpmfCode
      ((.x5 ↦ᵣ o5) ** (.x6 ↦ᵣ o6) ** (.x7 ↦ᵣ o7) ** (IterI ↦ₘ iWord) **
        (.x20 ↦ᵣ codePtr) ** memOwn codePtr **
        (.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
        (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ (3 : Word)) ** (codePtr ↦ₘ ((iWord <<< 2) ||| (3 : Word))) **
        (IterI ↦ₘ iWord) ** (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iWord) **
        (.x7 ↦ᵣ ((iWord <<< 2) ||| (3 : Word))) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  -- [126-127] la x5, cvpmf_iter_i
  have hau := CodeReq.ofProg_mem_at D (D + 504) cvpmfProg 126
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.cvpmf_iter_i
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 504))) (by bv_omega)
    (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)
  have had := CodeReq.ofProg_mem_at D (D + 508) cvpmfProg 127
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.cvpmf_iter_i
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 504))) (by bv_omega)
    (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)
  have s0 := EvmAsm.Rv64.la_materialize_within (cr := cvpmfCode) .x5 o5 (D + 504) IterI
    (by decide) (by decide) hau had
  rw [show (D + 504 : Word) + 8 = D + 512 from by bv_omega] at s0
  -- [128] ld x6, 0(x5)
  have s1 := ld_spec_gen_within .x6 .x5 IterI o6 iWord (0 : BitVec 12) (D + 512) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s1
  -- [129-130] slli x7, x6, 2 ;; ori x7, x7, 3
  have s2 := slli_spec_gen_within .x7 .x6 o7 iWord (2 : BitVec 6) (D + 516) (by decide)
  rw [show ((2 : BitVec 6).toNat) = 2 from by decide] at s2
  have s3 := ori_spec_gen_same_within .x7 (iWord <<< 2) (3 : BitVec 12) (D + 520) (by decide)
  rw [show signExtend12 (3 : BitVec 12) = (3 : Word) from by decide] at s3
  -- [131] sd x7, 0(x20)
  have s4 := sd_spec_gen_own_within .x20 .x7 codePtr ((iWord <<< 2) ||| (3 : Word))
    (0 : BitVec 12) (D + 524)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show codePtr + (0 : Word) = codePtr from by bv_omega] at s4
  -- [132] li a0, 3 ;; [133] j epilogue
  have s5 := li_spec_gen_within .x10 o10 (3 : Word) (D + 528) (by decide)
  have s6 := jal_x0_spec_gen_within (28 : BitVec 21) (D + 532)
  rw [show (D + 532) + signExtend21 (28 : BitVec 21) = D + 560 from by
    rw [show signExtend21 (28 : BitVec 21) = (28 : Word) from by decide]; bv_omega] at s6
  have hs0F := cpsTripleWithin_frameR
    ((IterI ↦ₘ iWord) ** (.x6 ↦ᵣ o6) ** (.x7 ↦ᵣ o7) ** (.x20 ↦ᵣ codePtr) **
      memOwn codePtr ** (.x10 ↦ᵣ o10)) (by pcfx) s0
  have hrest : cpsTripleWithin 6 (D + 512) (D + 560) cvpmfCode
      ((.x5 ↦ᵣ IterI) ** (IterI ↦ₘ iWord) ** (.x6 ↦ᵣ o6) ** (.x7 ↦ᵣ o7) **
        (.x20 ↦ᵣ codePtr) ** memOwn codePtr ** (.x10 ↦ᵣ o10))
      ((.x5 ↦ᵣ IterI) ** (IterI ↦ₘ iWord) ** (.x6 ↦ᵣ iWord) **
        (.x7 ↦ᵣ ((iWord <<< 2) ||| (3 : Word))) ** (.x20 ↦ᵣ codePtr) **
        (codePtr ↦ₘ ((iWord <<< 2) ||| (3 : Word))) ** (.x10 ↦ᵣ (3 : Word))) := by
    runBlock s1 s2 s3 s4 s5 s6
  have hblock := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs0F hrest
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) **
      (.x19 ↦ᵣ o19) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) (by pcfx) hblock
  have hepi := cvpmfEpilogue sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 codePtr o21 hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (3 : Word)) ** (codePtr ↦ₘ ((iWord <<< 2) ||| (3 : Word))) **
      (IterI ↦ₘ iWord) ** (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iWord) **
      (.x7 ↦ᵣ ((iWord <<< 2) ||| (3 : Word))) ** G)
    (by pcfx) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Exit 6 — callee-status propagation (idx 134–138, `D+536 → ra`)

    ⚠️ `*codePtr := i` **unshifted and untagged**, and `a0` is left exactly as the
    callee returned it — this arm mints no status of its own.  That is the Lean-level
    statement of discrepancies 1 and 3 in this module's header. -/

set_option maxRecDepth 8000 in
theorem cvpmfRetPropagate
    (sp0 spC raIn iWord codePtr cs0 cs1 cs2 cs3 cs4 cs5 : Word)
    (G : Assertion) (hG : G.pcFree) (o5 o6 status o1 o8 o9 o18 o19 o21 : Word)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn) :
    cpsTripleWithin 14 (D + 536) raIn cvpmfCode
      ((.x5 ↦ᵣ o5) ** (.x6 ↦ᵣ o6) ** (IterI ↦ₘ iWord) **
        (.x20 ↦ᵣ codePtr) ** memOwn codePtr **
        (.x10 ↦ᵣ status) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) **
        (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) ** (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) **
        (.x21 ↦ᵣ o21) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G)
      ((.x10 ↦ᵣ status) ** (codePtr ↦ₘ iWord) ** (IterI ↦ₘ iWord) **
        (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iWord) ** (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) ** (.x18 ↦ᵣ cs2) **
        (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) := by
  have hau := CodeReq.ofProg_mem_at D (D + 536) cvpmfProg 134
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.cvpmf_iter_i
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 536))) (by bv_omega)
    (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)
  have had := CodeReq.ofProg_mem_at D (D + 540) cvpmfProg 135
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.cvpmf_iter_i
      (ChainValidateOfflineAddrs.chain_validate_post_merge_full + 536))) (by bv_omega)
    (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)
  have s0 := EvmAsm.Rv64.la_materialize_within (cr := cvpmfCode) .x5 o5 (D + 536) IterI
    (by decide) (by decide) hau had
  rw [show (D + 536 : Word) + 8 = D + 544 from by bv_omega] at s0
  have s1 := ld_spec_gen_within .x6 .x5 IterI o6 iWord (0 : BitVec 12) (D + 544) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show IterI + (0 : Word) = IterI from by bv_omega] at s1
  have s2 := sd_spec_gen_own_within .x20 .x6 codePtr iWord (0 : BitVec 12) (D + 548)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show codePtr + (0 : Word) = codePtr from by bv_omega] at s2
  have s3 := jal_x0_spec_gen_within (8 : BitVec 21) (D + 552)
  rw [show (D + 552) + signExtend21 (8 : BitVec 21) = D + 560 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at s3
  have hs0F := cpsTripleWithin_frameR
    ((IterI ↦ₘ iWord) ** (.x6 ↦ᵣ o6) ** (.x20 ↦ᵣ codePtr) ** memOwn codePtr)
    (by pcfx) s0
  have hrest : cpsTripleWithin 3 (D + 544) (D + 560) cvpmfCode
      ((.x5 ↦ᵣ IterI) ** (IterI ↦ₘ iWord) ** (.x6 ↦ᵣ o6) **
        (.x20 ↦ᵣ codePtr) ** memOwn codePtr)
      ((.x5 ↦ᵣ IterI) ** (IterI ↦ₘ iWord) ** (.x6 ↦ᵣ iWord) **
        (.x20 ↦ᵣ codePtr) ** (codePtr ↦ₘ iWord)) := by
    runBlock s1 s2 s3
  have hblock := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs0F hrest
  have hblockF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ status) ** (.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ o1) ** (.x8 ↦ᵣ o8) ** (.x9 ↦ᵣ o9) **
      (.x18 ↦ᵣ o18) ** (.x19 ↦ᵣ o19) ** (.x21 ↦ᵣ o21) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
      ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) ** G) (by pcfx) hblock
  have hepi := cvpmfEpilogue sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    o1 o8 o9 o18 o19 codePtr o21 hspC hret
  have hepiF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ status) ** (codePtr ↦ₘ iWord) ** (IterI ↦ₘ iWord) **
      (.x5 ↦ᵣ IterI) ** (.x6 ↦ᵣ iWord) ** G)
    (by pcfx) hepi
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepiF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## The whole-routine triple, domain-restricted to `N = 0`

    `D → prologue → guard taken → all-valid exit → epilogue → ra`, 28 steps, no callee
    involved.  The `∀`-over-headers verdict is carried in the post; at `encoded = []`
    it is vacuous, which is exactly what the routine computes there (its own docstring
    calls the family "vacuous-true on N = 0"). -/

set_option maxRecDepth 8000 in
theorem chain_validate_post_merge_full_spec_within_empty
    (sp0 spC nWord lenBase hdrBase validPtr codePtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 : Word)
    (encoded : List EvmAsm.Stateless.SpecRef.Bytes)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-56 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hN : encoded = [])
    (hnWord : nWord = BitVec.ofNat 64 encoded.length) :
    cpsTripleWithin 28 D raIn cvpmfCode
      (((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
          (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
          (.x10 ↦ᵣ nWord) ** (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) **
          (.x13 ↦ᵣ validPtr) ** (.x14 ↦ᵣ codePtr) ** (.x5 ↦ᵣ old5) **
          (.x0 ↦ᵣ (0 : Word)) **
          memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
          memOwn (spC + 32) ** memOwn (spC + 40) ** memOwn (spC + 48) **
          memOwn validPtr ** memOwn codePtr) ** G)
      (⌜∀ eh ∈ encoded, PostMergeHeaderOk eh⌝ **
        (.x10 ↦ᵣ (0 : Word)) ** (validPtr ↦ₘ (1 : Word)) ** (codePtr ↦ₘ (0 : Word)) **
        (.x1 ↦ᵣ raIn) ** (.x2 ↦ᵣ sp0) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) **
        ((spC + 40) ↦ₘ cs4) ** ((spC + 48) ↦ₘ cs5) **
        (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) **
        (.x14 ↦ᵣ codePtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** G) := by
  subst hN
  have hz : nWord = (0 : Word) := by rw [hnWord]; decide
  subst hz
  -- prologue, framed by the caller's `G`
  have hpro := cpsTripleWithin_frameR G hG
    (cvpmfPrologue sp0 spC (0 : Word) lenBase hdrBase validPtr codePtr raIn
      cs0 cs1 cs2 cs3 cs4 cs5 old5 hspC)
  -- guard `beq x21, x8` taken (`i = 0 = N`)
  have hbeq := beq_spec_gen_within .x21 .x8 (488 : BitVec 13) (0 : Word) (0 : Word) (D + 68)
  have hbeqC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at D (D + 68) cvpmfProg 17 (.BEQ .x21 .x8 (488 : BitVec 13))
      (by bv_omega) (by rw [cvpmf_length]; decide) rfl (by rw [cvpmf_length]; decide)) hbeq
  have htaken := cpsBranchWithin_takenStripPure2 hbeqC (fun hp hq => by
    obtain ⟨_, _, _, _, _, hrest⟩ := hq
    exact absurd rfl ((sepConj_pure_right _).1 hrest).2)
  rw [show (D + 68) + signExtend13 (488 : BitVec 13) = D + 556 from by
    rw [show signExtend13 (488 : BitVec 13) = (488 : Word) from by decide]; bv_omega] at htaken
  have htakenF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ raIn) ** (.x9 ↦ᵣ lenBase) ** (.x18 ↦ᵣ hdrBase) **
      (.x19 ↦ᵣ validPtr) ** (.x20 ↦ᵣ codePtr) ** (.x10 ↦ᵣ (0 : Word)) **
      (.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) **
      (.x14 ↦ᵣ codePtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
      ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
      ((spC + 48) ↦ₘ cs5) ** (validPtr ↦ₘ (1 : Word)) ** (codePtr ↦ₘ (0 : Word)) ** G)
    (by pcfx) htaken
  -- all-valid exit + epilogue
  have hav := cvpmfRetAllValid sp0 spC raIn cs0 cs1 cs2 cs3 cs4 cs5
    ((.x11 ↦ᵣ lenBase) ** (.x12 ↦ᵣ hdrBase) ** (.x13 ↦ᵣ validPtr) **
      (.x14 ↦ᵣ codePtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      (validPtr ↦ₘ (1 : Word)) ** (codePtr ↦ₘ (0 : Word)) ** G)
    (by pcfx) (0 : Word) raIn (0 : Word) lenBase hdrBase validPtr codePtr (0 : Word)
    hspC hret
  have hstep1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hpro htakenF
  have hstep2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hstep1 hav
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hstep2
  refine (sepConj_pure_left h).mpr ⟨?_, by xperm_hyp hq⟩
  intro eh heh
  exact absurd heh (by simp)

/-! ## Residuals — named, not proved

    Per the issue's scope discipline: a rule that cannot be pinned is named as its own
    `Prop` rather than absorbed by weakening a postcondition. -/

open EvmAsm.Stateless.SpecRef in
/-- **Residual R1 — the keccak tie.**  The baked 32 bytes at `cvpmf_empty_hash` are the
    reference's `EMPTY_OMMER_HASH = keccak256 (rlp.encode [])`.

    NOT provable here: `decide` on `keccak256` exhausts the recursion limit
    (see `Programs/AccountDecodeCorrespondence.lean`, which discharges the *account*
    sentinels only by isolating a concrete one-block absorption against a pre-existing
    `keccakF` KAT).  Closing R1 means supplying the analogous KAT for the one-byte
    input `[0xc0]`; the drift gates above (`cvpmfEmptyOmmerHashBytes_value`,
    `cvpmfEmptyOmmerHash_dword0..3`) are what stands in for it in the meantime, and
    they catch literal drift but not a wrong-by-construction literal. -/
def EmptyOmmerHashPinned : Prop :=
  EMPTY_OMMER_HASH = cvpmfEmptyOmmerHashBytes

/-! ### The two gaps that are NOT residual `Prop`s, and why

    **The loop (`N ≥ 1`).**  This is proof engineering, not an unpinnable rule: all
    three rules' exit behaviours ARE pinned, by `cvpmfRetDifficulty` / `cvpmfRetNonce` /
    `cvpmfRetOmmers` above.  What is missing is the induction from `D+68` that composes
    them, which needs `rlpFieldToU64_spec_within` threaded twice and
    `rlpListNthItem_spec_within` once per iteration plus a four-dword region compare.
    The gap is therefore written into the *statement* — `hN : encoded = []` on
    `chain_validate_post_merge_full_spec_within_empty` — rather than dressed up as a
    `Prop`, because any `Prop` short enough to state here would either be provable by
    pure list reasoning (and so say nothing about the machine) or need the whole loop
    vocabulary it is standing in for.

    **The difficulty verdict shape.**  The port's `difficulty` is a `Uint`
    (`Stateless.lean:82`, `numericFieldWidths` carries `(7, none)`), so a header whose
    field 7 is 9+ bytes decodes fine and is rejected by `validate_header` as "difficulty
    nonzero".  The guest cannot report that as a rule violation: `rlp_field_to_u64`
    fails on a field wider than 8 bytes, so the routine takes the propagate arm
    (`D+536`), which — per `cvpmfRetPropagate` — returns the callee's nonzero status and
    leaves `*validPtr` alone.  Sound for a caller that tests `a0` before reading
    `*validPtr`; a divergence in verdict *shape* for one that does not.  No analogous
    gap exists for `nonce` (fixed 8 bytes, and `nonce_rule_agrees` closes it) or for
    `ommers_hash` (fixed 32, and the guest checks the width itself at `D+308`). -/

end EvmAsm.Codegen.ChainValidatePostMergeFullSpec
