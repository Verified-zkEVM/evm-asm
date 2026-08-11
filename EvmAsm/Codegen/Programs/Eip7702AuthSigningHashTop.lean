/-
  EvmAsm.Codegen.Programs.Eip7702AuthSigningHashTop

  **First whole-routine triple on the signing-hash lane (#12038):**
  `eip7702_authorization_signing_hash` (K147) at
  `GuestAddrs.eip7702_authorization_signing_hash`, over the emitted
  `eip7702AuthorizationSigningHash_prog` (9 instructions).

  ## What is proved here

  The routine is the typed wrapper for the EIP-7702 per-authorization signing
  hash.  It owns exactly three decisions, and this module proves all three
  against the machine:

    1. the retained-field count is `3` (`a2 := 3`),
    2. the type-prefix byte is the EIP-7702 authorization MAGIC `0x05`
       (`a3 := 5`),
    3. the caller's 32-byte output pointer is forwarded from `a2` to `a4`
       (`a4 := a2`, done BEFORE `a2` is overwritten by the field count).

  Everything else is delegated to `tx_signing_hash` by one cross-`jal`.

  ## The residual (an UNPROVEN-CALLEE DEPENDENCY, not an input-domain gate)

  `tx_signing_hash` (K145, 93 instructions) has **no** machine triple, so the
  call is carried as the named residual `txSigningHashContract` — the shape
  established by `MptWalkResiduals.wlCallWithinShape` and
  `ExecutionRequestsHashShaResidual.shaCallWithinShape`.  Per the 2026-08-11
  coord rule an unproven-callee residual is a DEPENDENCY: it is named in the
  statement, it is not folded into a conditional gate list, and it retires when
  `tx_signing_hash_spec_within` lands.

  ⚠️ Two things about this residual that are easy to get wrong:

  * It is deliberately **generic in `(n_fields, type_prefix)`** — a
    `∀ nW prefixW, nW.toNat ≤ fields.length → …` family, because that is the
    real contract of `tx_signing_hash`, which is a shared helper for the whole
    typed-tx table (legacy 6 / 2930 8 / 1559 9 / 4844 11 / 7702 10).  The
    wrapper's `3` and `0x05` are therefore **derived from the machine**, not
    assumed: a `LI` of any other immediate would leave the goal unclosable.
    The `nW.toNat ≤ fields.length` side condition is load-bearing and keeps the
    family satisfiable — beyond it the callee returns status 1 and writes no
    hash, so a `∀ nW` with no bound would be a FALSE hypothesis.
  * Its post is stated in **pure SpecRef terms** (`SpecRef.keccak256` of the
    preimage), not operationally.  So the keccak leg of THIS theorem is already
    SpecRef-facing; #12104's `keccakBodyDigest_eq_specref` is what will let the
    eventual `tx_signing_hash_spec_within` discharge into this form.  It cannot
    be used here: `tx_signing_hash` hashes through `zkvm_keccak256_segments`
    (a 3-segment gather entry point with NO triple and no registry row), not
    through `zkvm_keccak256`, so there is no `keccakBodyDigest` to rewrite at
    this level.

  ## The SpecRef tie is by reduction, not by transcription

  `authSigningHash` is not a hand-copied preimage: `recover_authority_unfold`
  below is proved by `rfl` and exhibits `authSigningHash auth` sitting in the
  exact position of `SpecRef.recover_authority`'s `signing_hash` local
  (`Stateless/SpecRef/Interpreter.lean`, `recover_authority`).  Note that the
  EIP-7702 *authorization* hash is NOT one of the six
  `SpecRef.Transactions.signing_hash_*` functions — those are the transaction
  signing hashes; the authorization digest lives inline in `recover_authority`
  and is keyed on `SET_CODE_TX_MAGIC`.

  No elaboration budget is widened anywhere in this module.
-/

import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.MemRegion
import EvmAsm.Stateless.SpecRef.Interpreter

namespace EvmAsm.Codegen.Eip7702AuthSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.EL
open EvmAsm.Stateless.SpecRef

/-! ## Guest addresses and the routine's frame decomposition -/

/-- Entry of the wrapper. -/
abbrev AuthB : Word := BitVec.ofNat 64 GuestAddrs.eip7702_authorization_signing_hash

/-- Entry of the residual callee `tx_signing_hash` (K145). -/
abbrev TshB : Word := BitVec.ofNat 64 GuestAddrs.tx_signing_hash

/-- The wrapper's saved-register frame: `ra` only, at `newSp + 0`. -/
def authFrame : FrameDesc := [(.x1, (0 : BitVec 12))]

/-- The emitted cross-`jal` offset to `tx_signing_hash` (site at `AuthB + 20`). -/
def authJalOff : BitVec 21 :=
  jalOff GuestAddrs.tx_signing_hash (GuestAddrs.eip7702_authorization_signing_hash + 20)

/-- The wrapper's body: argument marshalling then the cross-call.
    `MV a4, a2` runs FIRST — before `a2` is clobbered with the field count. -/
def authBody : List Instr :=
  [ .MV .x14 .x12, .LI .x12 (3 : Word), .LI .x13 (5 : Word), .JAL .x1 authJalOff ]

/-- Kernel-checked structural drift guard: the emitted routine IS the standard
    `sp-16` / save-`ra` ABI frame around `authBody`.  If codegen re-emits the
    routine with a different frame size, a different saved-register set, or a
    different body, this `rfl` breaks and every triple below fails with it. -/
theorem eip7702AuthorizationSigningHash_prog_eq_frame :
    eip7702AuthorizationSigningHash_prog
      = abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) authFrame authBody := rfl

/-- The code requirement the triples run against: the REAL emitted program at
    its REAL guest address.  Every triple below mentions this. -/
abbrev authCode : CodeReq :=
  CodeReq.ofProg AuthB eip7702AuthorizationSigningHash_prog

/-- Address of the cross-`jal` instruction. -/
abbrev authJalPC : Word := AuthB + BitVec.ofNat 64 20

/-- The `jal` resolves to `tx_signing_hash`. Kernel-checked at the linked
    guest addresses, so a relocation drift is caught here. -/
theorem authJal_target : authJalPC + signExtend21 authJalOff = TshB := by
  unfold authJalPC authJalOff AuthB TshB; decide

theorem authJal_ret_even : ((authJalPC + 4) &&& ~~~(1 : Word)) = authJalPC + 4 := by
  unfold authJalPC AuthB; decide

/-! ## The reference digest, tied to `SpecRef.recover_authority` by reduction -/

/-- The six RLP fields of a signed EIP-7702 authorization tuple, in wire order:
    `[chain_id, address, nonce, y_parity, r, s]`.  This is the list
    `SpecRef.Transactions.decodeItemAuthorization` consumes (see
    `sampleAuth_decodes` for the kernel-checked confirmation);
    `Transactions.authItem` builds the same list but is `private`, so the tie is
    made through the public decoder instead. -/
def authTupleFields (auth : Authorization) : List RLP.RLPItem :=
  [ .bytes (RLP.Nat.toBytesBE auth.chainId),
    .bytes auth.address,
    .bytes (RLP.Nat.toBytesBE auth.nonce),
    .bytes (RLP.Nat.toBytesBE auth.yParity),
    .bytes (RLP.Nat.toBytesBE auth.r),
    .bytes (RLP.Nat.toBytesBE auth.s) ]

/-- The full signed authorization tuple as it appears on the wire — the guest's
    `a0`/`a1` input region. -/
def authTupleRlp (auth : Authorization) : List (BitVec 8) :=
  RLP.encode (.list (authTupleFields auth))

/-- The EIP-7702 authorization signing preimage:
    `MAGIC(0x05) ‖ rlp([chain_id, address, nonce])`. -/
def authSigningPreimage (auth : Authorization) : List (BitVec 8) :=
  SET_CODE_TX_MAGIC ++ RLP.encode (.list
    [ .bytes (RLP.Nat.toBytesBE auth.chainId),
      .bytes auth.address,
      .bytes (RLP.Nat.toBytesBE auth.nonce) ])

/-- The EIP-7702 authorization signing hash. -/
def authSigningHash (auth : Authorization) : Hash32 :=
  keccak256 (authSigningPreimage auth)

/-- **The SpecRef tie, by reduction.** `authSigningHash auth` occupies exactly
    the position of the `signing_hash` local inside
    `SpecRef.recover_authority`; proved by `rfl`, so it is not a transcription
    of the preimage but the same term. If `recover_authority` changes its
    digest, this breaks. -/
theorem recover_authority_unfold (auth : Authorization) :
    recover_authority auth =
      (if auth.yParity ≠ 0 && auth.yParity ≠ 1 then none
       else if auth.r == 0 || auth.r ≥ SECP256K1N then none
       else if auth.s == 0 || auth.s > SECP256K1N / 2 then none
       else
         match Secp256k1.recover (bytesBEtoNat (authSigningHash auth))
             auth.r auth.s auth.yParity with
         | .ok (x, y) => some ((keccak256 (natToBytesBE 32 x ++ natToBytesBE 32 y)).drop 12)
         | .error _ => none) := rfl

/-- The signing preimage is the 6-field tuple truncated to its first three
    fields, prefixed by MAGIC — i.e. exactly what a `(n = 3, prefix = 0x05)`
    call to `tx_signing_hash` computes. -/
theorem authSigningPreimage_eq_take3 (auth : Authorization) :
    authSigningPreimage auth
      = SET_CODE_TX_MAGIC ++ RLP.encode (.list ((authTupleFields auth).take 3)) := rfl

/-- **Field-position pinning.** Each field occupies its OWN contiguous byte
    range of the preimage, in wire order, so the statement is not symmetric in
    any two fields: swapping `chain_id` and `address` changes these bytes.
    (`hshort` is the ≤ 55-byte short-list form, which every real authorization
    takes: 1 + ≤33 + 21 + ≤9 = at most 64 — see the concrete instance below,
    and note that only the short form is pinned here.) -/
theorem authSigningPreimage_segments (auth : Authorization)
    (hshort : (RLP.encode.encodeItems
      [ .bytes (RLP.Nat.toBytesBE auth.chainId),
        .bytes auth.address,
        .bytes (RLP.Nat.toBytesBE auth.nonce) ]).length ≤ 55) :
    authSigningPreimage auth
      = (0x05 : BitVec 8)
        :: BitVec.ofNat 8 (0xC0 + (RLP.encodeBytes (RLP.Nat.toBytesBE auth.chainId)
              ++ RLP.encodeBytes auth.address
              ++ RLP.encodeBytes (RLP.Nat.toBytesBE auth.nonce)).length)
        :: (RLP.encodeBytes (RLP.Nat.toBytesBE auth.chainId)
              ++ RLP.encodeBytes auth.address
              ++ RLP.encodeBytes (RLP.Nat.toBytesBE auth.nonce)) := by
  simp only [authSigningPreimage, SET_CODE_TX_MAGIC, RLP.encode,
    RLP.encode.encodeItems, List.append_assoc, List.append_nil] at hshort ⊢
  simp only [hshort, if_pos]
  rfl

/-! ## The named residual: `tx_signing_hash`'s calling contract

`tx_signing_hash` guest ABI (`Programs/TxSigningHash.lean`, K145):
`a0` inner-RLP ptr, `a1` its byte length, `a2` retained field count,
`a3` type-prefix byte (`0` = no prefix), `a4` 32-byte output ptr;
`a0 = 0` on success, `1` on RLP-parse failure / fewer than `a2` fields.
Its own frame is `sp-64`, hence `stackFree … 8`.  Callee-saved `x8/x9/x18-x22`
and temps `x5-x7/x28-x31` pass through `F`, matching `shaCallWithinShape`. -/

/-- The preimage `tx_signing_hash` hashes: the optional single type-prefix byte
    (included iff `a3 ≠ 0`, per the `BEQ a3, x0` segment-length select) followed
    by the freshly re-encoded RLP list of the first `a2` retained fields. -/
def tshPreimage (prefixW nW : Word) (fields : List RLP.RLPItem) : List (BitVec 8) :=
  (if prefixW = 0 then [] else [BitVec.ofNat 8 prefixW.toNat])
    ++ RLP.encode (.list (fields.take nW.toNat))

/-- Call-site entry ambient for `tx_signing_hash`. -/
def tshCallEntry (sp0 inPtr lenW nW prefixW outPtr : Word)
    (inBytes outOld : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ nW) **
  (.x13 ↦ᵣ prefixW) ** (.x14 ↦ᵣ outPtr) **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inPtr inBytes ** bytesRegion outPtr outOld

/-- Call-site return ambient after `tx_signing_hash`: success status in `a0`,
    input region intact, output region holding the 32-byte digest. -/
def tshCallReturn (sp0 inPtr outPtr : Word)
    (inBytes hashBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
  (.x10 ↦ᵣ (0 : Word)) **
  regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
  (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inPtr inBytes ** bytesRegion outPtr hashBytes

/-- The six NON-TRIPLE side conditions of the residual, split out so they can be
    discharged concretely — this is where a vacuity trap would hide, and
    `authCallSite_ok` below closes all six at the real call site.  Five are
    decidable at concrete data; the sixth (`F.pcFree`) is discharged
    structurally. -/
def tshCallSiteOk (cr : CodeReq) (callerPC lenW : Word)
    (fields : List RLP.RLPItem) (outOld : List (BitVec 8))
    (offset : BitVec 21) (F : Assertion) : Prop :=
  F.pcFree ∧
  ((callerPC + 4) &&& ~~~(1 : Word)) = callerPC + 4 ∧
  callerPC + signExtend21 offset = TshB ∧
  (∀ a i, CodeReq.singleton callerPC (.JAL .x1 offset) a = some i → cr a = some i) ∧
  lenW.toNat = (RLP.encode (.list fields)).length ∧
  outOld.length = 32

/-- **The named residual.** `tx_signing_hash`'s whole-routine calling contract
    at one `callWithin` site, GENERIC in the retained-field count and the
    type-prefix byte (that genericity is the point — see the module docstring).

    ⛔ NOT an input-domain gate: an unproven-callee DEPENDENCY.
    **Discharge owner:** a machine triple `tx_signing_hash_spec_within` at
    `GuestAddrs.tx_signing_hash`, which in turn needs a triple for
    `zkvm_keccak256_segments` (no row today); its pure keccak leg then closes
    against #12104 `keccakBodyDigest_eq_specref`.
    ⚠️ The discharge owner above is named by SYMBOL deliberately: #12038 was the
    tracking issue and was closed 2026-08-11 while this was in flight, so the
    issue number is not a reliable handle. The obligation is real regardless of
    which issue carries it — `tx_signing_hash_spec_within` either exists or it
    does not. -/
def txSigningHashContract (cr : CodeReq) (callerPC vOld sp0 inPtr lenW outPtr : Word)
    (fields : List RLP.RLPItem) (outOld : List (BitVec 8))
    (offset : BitVec 21) (fuel : Nat) (F : Assertion) : Prop :=
  tshCallSiteOk cr callerPC lenW fields outOld offset F ∧
  ∀ nW prefixW : Word, nW.toNat ≤ fields.length →
    cpsTripleWithin (1 + fuel) callerPC (callerPC + 4) cr
      (((.x1 ↦ᵣ vOld) ** tshCallEntry sp0 inPtr lenW nW prefixW outPtr
          (RLP.encode (.list fields)) outOld) ** F)
      (((.x1 ↦ᵣ (callerPC + 4)) ** tshCallReturn sp0 inPtr outPtr
          (RLP.encode (.list fields))
          (keccak256 (tshPreimage prefixW nW fields))) ** F)

/-- Obligation-retirement note, rendered into `Progress.Obligations`. -/
def txSigningHashResidualNote : String :=
  "machine triple `tx_signing_hash_spec_within` at GuestAddrs.tx_signing_hash \
(93 insn, K145), registered in Routines + Correspondence; the K147 wrapper site \
at eip7702_authorization_signing_hash+20 then discharges via callWithin against \
that triple (txSigningHashContract). Blocked in turn on a triple for \
zkvm_keccak256_segments (3-segment gather entry point, NO registry row); its \
pure keccak leg closes against #12104 keccakBodyDigest_eq_specref. Until then: \
UNPROVEN-CALLEE residual DEPENDENCY, not an input-domain gate; grade names \
tx_signing_hash. The hole is identified by the SYMBOL above, not by an issue \
number: #12038 tracked it and was closed 2026-08-11 mid-flight, so the \
obligation outlives its tracker."

/-! ## The wrapper's caller-visible footprint -/

/-- Entry register values of the wrapper's frame: `ra ↦ ret`. -/
def authVals (ret : Word) : Reg → Word :=
  fun r => match r with | .x1 => ret | _ => 0

/-- Post-body values: `ra` genuinely clobbered by the `jal` (link `AuthB + 24`);
    the epilogue restores it from the frame slot. -/
def authVals' : Reg → Word :=
  fun r => match r with | .x1 => AuthB + BitVec.ofNat 64 24 | _ => 0

/-- Caller-visible precondition: the callee's free stack, the guest ABI
    registers (`a0` tuple ptr, `a1` its length, `a2` output ptr — and the two
    scratch args `a3`/`a4` the wrapper is about to load), the authorization
    tuple's byte region and the 32-byte output region. -/
def authCallerPre (newSp inPtr lenW outPtr x13Old x14Old : Word)
    (inBytes outOld : List (BitVec 8)) (F : Assertion) : Assertion :=
  stackFree newSp 8 **
  (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outPtr) **
  (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old) ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inPtr inBytes ** bytesRegion outPtr outOld ** F

/-- Caller-visible postcondition: status `0` in `a0`, the tuple region intact,
    and the output region holding `hashBytes`. -/
def authCallerPost (newSp inPtr outPtr : Word)
    (inBytes hashBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  stackFree newSp 8 **
  (.x10 ↦ᵣ (0 : Word)) ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
  regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
  bytesRegion inPtr inBytes ** bytesRegion outPtr hashBytes ** F

/-- What the callee cannot touch at the call site: the wrapper's saved-`ra`
    slot, plus the caller's own frame `F`. -/
def authResidualFrame (newSp ret : Word) (F : Assertion) : Assertion :=
  ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ ret) ** F

theorem authResidualFrame_pcFree (newSp ret : Word) (F : Assertion) (hF : F.pcFree) :
    (authResidualFrame newSp ret F).pcFree :=
  pcFree_sepConj pcFree_memIs hF

theorem authCallerPre_pcFree (newSp inPtr lenW outPtr x13Old x14Old : Word)
    (inBytes outOld : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (authCallerPre newSp inPtr lenW outPtr x13Old x14Old inBytes outOld F).pcFree := by
  unfold authCallerPre
  repeat' first
    | exact hF | exact pcFree_regIs | exact bytesRegion_pcFree _ _
    | exact pcFree_stackFree _ _ | apply pcFree_sepConj

theorem authCallerPost_pcFree (newSp inPtr outPtr : Word)
    (inBytes hashBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (authCallerPost newSp inPtr outPtr inBytes hashBytes F).pcFree := by
  unfold authCallerPost
  repeat' first
    | exact hF | exact pcFree_regIs | exact pcFree_regOwn
    | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
    | apply pcFree_sepConj

/-! ## The wrapper's two owned facts, at `n = 3` / `prefix = 0x05` -/

/-- The `(n = 3, prefix = 0x05)` instance of the callee's generic preimage IS
    the EIP-7702 authorization signing preimage. This is the step that consumes
    the two immediates the wrapper's `LI`s put in `a2`/`a3`. -/
theorem tshPreimage_at_7702 (auth : Authorization) :
    tshPreimage (5 : Word) (3 : Word) (authTupleFields auth)
      = authSigningPreimage auth := rfl

/-- Field count `3` is within the six-field authorization tuple — the residual
    family's side condition at this site. -/
theorem three_le_authTupleFields (auth : Authorization) :
    (3 : Word).toNat ≤ (authTupleFields auth).length := by
  simp [authTupleFields]

/-! ## The body triple -/

/-- The three marshalling instructions as a slice, for code-membership. -/
private def authMarshalSeg : List Instr :=
  [ .MV .x14 .x12, .LI .x12 (3 : Word), .LI .x13 (5 : Word) ]

private theorem authMarshalCore (outPtr x13Old x14Old : Word) :
    cpsTripleWithin 3 (AuthB + BitVec.ofNat 64 8)
      (AuthB + BitVec.ofNat 64 8 + 4 + 4 + 4)
      (CodeReq.ofProg (AuthB + BitVec.ofNat 64 8) authMarshalSeg)
      ((.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old))
      ((.x12 ↦ᵣ (3 : Word)) ** (.x13 ↦ᵣ (5 : Word)) ** (.x14 ↦ᵣ outPtr)) := by
  simp only [authMarshalSeg, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  have hmv := mv_spec_gen_within .x14 .x12 outPtr x14Old
    (AuthB + BitVec.ofNat 64 8) (by decide)
  have hli1 := li_spec_gen_within .x12 outPtr (3 : Word)
    (AuthB + BitVec.ofNat 64 8 + 4) (by decide)
  have hli2 := li_spec_gen_within .x13 x13Old (5 : Word)
    (AuthB + BitVec.ofNat 64 8 + 4 + 4) (by decide)
  runBlock hmv hli1 hli2

/-- Argument marshalling, over the REAL routine code: `a4 := a2` (the caller's
    output pointer, copied out BEFORE `a2` is overwritten), `a2 := 3`,
    `a3 := 5`. -/
private theorem authMarshal (outPtr x13Old x14Old : Word) :
    cpsTripleWithin 3 (AuthB + BitVec.ofNat 64 8) authJalPC authCode
      ((.x12 ↦ᵣ outPtr) ** (.x13 ↦ᵣ x13Old) ** (.x14 ↦ᵣ x14Old))
      ((.x12 ↦ᵣ (3 : Word)) ** (.x13 ↦ᵣ (5 : Word)) ** (.x14 ↦ᵣ outPtr)) := by
  rw [show authJalPC = AuthB + BitVec.ofNat 64 8 + 4 + 4 + 4 from by
    unfold authJalPC AuthB; decide]
  exact cpsTripleWithin_extend_code (by code_mem) (authMarshalCore outPtr x13Old x14Old)

/-- Everything the marshalling instructions do not own, framed across them. -/
private def authSiteFrame (newSp ret inPtr lenW outPtr : Word)
    (inBytes outOld : List (BitVec 8)) (F : Assertion) : Assertion :=
  (.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret)
  ** ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
  ** stackFree newSp 8 ** (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))
  ** bytesRegion inPtr inBytes ** bytesRegion outPtr outOld ** F

private theorem authSiteFrame_pcFree (newSp ret inPtr lenW outPtr : Word)
    (inBytes outOld : List (BitVec 8)) (F : Assertion) (hF : F.pcFree) :
    (authSiteFrame newSp ret inPtr lenW outPtr inBytes outOld F).pcFree := by
  unfold authSiteFrame
  repeat' first
    | exact hF | exact pcFree_regIs | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _ | exact pcFree_stackFree _ _
    | apply pcFree_sepConj

/-- The `(n = 3, prefix = 0x05)` digest the residual delivers IS the EIP-7702
    authorization signing hash. -/
private theorem authDigest_eq (auth : Authorization) :
    keccak256 (tshPreimage (5 : Word) (3 : Word) (authTupleFields auth))
      = authSigningHash auth := by
  rw [tshPreimage_at_7702]; rfl

/-- `authTupleRlp` is the callee-contract's input byte string, by definition. -/
private theorem authTupleRlp_eq (auth : Authorization) :
    RLP.encode (.list (authTupleFields auth)) = authTupleRlp auth := rfl

/-- **The wrapper body**: marshalling then the residual cross-call, with the
    residual instantiated at `n = 3` and `prefix = 0x05` — the two immediates
    the machine's `LI`s supply. -/
private theorem authBody_triple (newSp ret inPtr lenW outPtr x13Old x14Old : Word)
    (auth : Authorization) (outOld : List (BitVec 8)) (fuel : Nat) (F : Assertion)
    (hF : F.pcFree)
    (h_tsh : txSigningHashContract authCode authJalPC ret newSp inPtr lenW outPtr
      (authTupleFields auth) outOld authJalOff fuel
      (authResidualFrame newSp ret F)) :
    cpsTripleWithin (3 + (1 + fuel)) (AuthB + BitVec.ofNat 64 8)
      (AuthB + BitVec.ofNat 64 24) authCode
      ((.x2 ↦ᵣ newSp) ** regsAt authFrame (authVals ret)
        ** frameSlotsSaved authFrame newSp (authVals ret)
        ** authCallerPre newSp inPtr lenW outPtr x13Old x14Old
             (authTupleRlp auth) outOld F)
      ((.x2 ↦ᵣ newSp) ** regsAt authFrame authVals'
        ** frameSlotsSaved authFrame newSp (authVals ret)
        ** authCallerPost newSp inPtr outPtr (authTupleRlp auth)
             (authSigningHash auth) F) := by
  obtain ⟨_hsite, htrip⟩ := h_tsh
  have hcall := htrip (3 : Word) (5 : Word) (three_le_authTupleFields auth)
  rw [authDigest_eq auth, authTupleRlp_eq auth] at hcall
  -- frame the marshalling over everything it does not own
  have hmarshF := cpsTripleWithin_frameR
    (authSiteFrame newSp ret inPtr lenW outPtr (authTupleRlp auth) outOld F)
    (authSiteFrame_pcFree newSp ret inPtr lenW outPtr (authTupleRlp auth) outOld F hF)
    (authMarshal outPtr x13Old x14Old)
  -- chain marshalling into the residual call
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      unfold authSiteFrame authResidualFrame tshCallEntry at *
      xperm_hyp hp)
    hmarshF hcall
  rw [show authJalPC + 4 = AuthB + BitVec.ofNat 64 24 from by
    unfold authJalPC AuthB; decide] at hchain
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hchain
  · simp only [authFrame, regsAt, frameSlotsSaved, authVals, authCallerPre,
      List.foldr_cons, List.foldr_nil, sepConj_emp_right'] at hp
    unfold authSiteFrame
    xperm_hyp hp
  · simp only [authFrame, regsAt, frameSlotsSaved, authVals, authVals',
      List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    unfold authCallerPost authResidualFrame tshCallReturn at *
    xperm_hyp hq

/-! ## The whole-routine triple -/

/-- Step budget: prologue `addi`+`sd` (2), marshalling (3), the residual call
    (`1 + fuel`), epilogue `ld`+`addi`+`ret` (3). -/
def authSteps (fuel : Nat) : Nat := 1 + 1 + (3 + (1 + fuel)) + 1 + 1 + 1

/-- **Whole-routine triple for `eip7702_authorization_signing_hash`** over the
    emitted `eip7702AuthorizationSigningHash_prog` at
    `GuestAddrs.eip7702_authorization_signing_hash`.

    Entered with the signed authorization tuple's RLP in `[a0, a1)` and a
    32-byte output buffer at `a2`, the routine returns to `ra` with `sp`/`ra`
    restored to entry, status `0` in `a0`, the tuple region intact, and the
    output region holding **`authSigningHash auth`** — the digest
    `SpecRef.recover_authority` feeds to `Secp256k1.recover`
    (`recover_authority_unfold`, by `rfl`).

    Hypotheses, classified:
    * `halign` — ABI obligation (the caller's return address is even).
    * `hF` — ordinary framing side condition.
    * `h_tsh` — the NAMED RESIDUAL `txSigningHashContract`: an
      UNPROVEN-CALLEE DEPENDENCY on `tx_signing_hash`, **not** an
      input-domain restriction. See the module docstring and
      `txSigningHashResidualNote`; every computable component of it is
      discharged at this very call site by `authCallSite_ok`.

    There is NO input-domain gate: `auth` ranges over all `Authorization`s and
    `sp0`/`inPtr`/`outPtr`/`lenW` over all words. -/
theorem eip7702_authorization_signing_hash_spec_within
    (sp0 ret inPtr lenW outPtr x13Old x14Old : Word)
    (auth : Authorization) (outOld : List (BitVec 8)) (fuel : Nat) (F : Assertion)
    (hF : F.pcFree)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (h_tsh : txSigningHashContract authCode authJalPC ret
      (sp0 + signExtend12 (-16 : BitVec 12)) inPtr lenW outPtr
      (authTupleFields auth) outOld authJalOff fuel
      (authResidualFrame (sp0 + signExtend12 (-16 : BitVec 12)) ret F)) :
    cpsTripleWithin (authSteps fuel) AuthB ret authCode
      ((.x2 ↦ᵣ sp0) ** regsAt authFrame (authVals ret)
        ** frameSlotsOwn authFrame (sp0 + signExtend12 (-16 : BitVec 12))
        ** authCallerPre (sp0 + signExtend12 (-16 : BitVec 12)) inPtr lenW outPtr
             x13Old x14Old (authTupleRlp auth) outOld F)
      ((.x2 ↦ᵣ sp0) ** regsAt authFrame (authVals ret)
        ** frameSlotsSaved authFrame (sp0 + signExtend12 (-16 : BitVec 12))
             (authVals ret)
        ** authCallerPost (sp0 + signExtend12 (-16 : BitVec 12)) inPtr outPtr
             (authTupleRlp auth) (authSigningHash auth) F) := by
  have hbody := authBody_triple (sp0 + signExtend12 (-16 : BitVec 12)) ret inPtr lenW
    outPtr x13Old x14Old auth outOld fuel F hF h_tsh
  rw [show AuthB + BitVec.ofNat 64 8
        = AuthB + BitVec.ofNat 64 (4 * (1 + authFrame.length)) from by decide,
     show AuthB + BitVec.ofNat 64 24
        = AuthB + BitVec.ofNat 64 (4 * (1 + authFrame.length + authBody.length))
        from by decide] at hbody
  unfold authSteps
  -- `abi_frame` verbatim, except `hcpF`/`hcpF'` need the caller's `hF`.
  exact abiFrame_spec
    (posImm := (16 : BitVec 12))
    (hframe := rfl)
    (hne := by decide)
    (hbound := by decide)
    (hprogBound := by decide)
    (hret := rfl)
    (halign := halign)
    (hframeRestore := sext_frameRestore _ _ _ (by decide))
    (hcpF := authCallerPre_pcFree _ inPtr lenW outPtr x13Old x14Old _ outOld F hF)
    (hcpF' := authCallerPost_pcFree _ inPtr outPtr _ _ F hF)
    (hsub := by code_mem)
    (hbody := hbody)

/-! ## Non-vacuity

The theorem above is only worth something if its hypotheses are satisfiable.
`halign` and `hF` are trivially so (`ret := 0`, `F := empAssertion`).  The
residual `h_tsh` cannot be *proved* here — that is the point of a residual —
but every one of its COMPUTABLE conjuncts is discharged below at the real call
site, which is where a vacuity trap would otherwise hide (cf. `jalr_sail_equiv`,
where 68 of 128 constructors of a bundled hypothesis hit an assert-false).  What
is left un-exhibited is exactly one `cpsTripleWithin` for `tx_signing_hash`. -/

/-- Every computable side condition of the residual holds at the real call site
    `eip7702_authorization_signing_hash + 20`: the `jal` reloc resolves to
    `tx_signing_hash`, the return address is even, the `jal` really is in the
    emitted image, and the frame is `pcFree`. -/
theorem authCallSite_ok (newSp ret lenW : Word) (fields : List RLP.RLPItem)
    (outOld : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (hlen : lenW.toNat = (RLP.encode (.list fields)).length)
    (hout : outOld.length = 32) :
    tshCallSiteOk authCode authJalPC lenW fields outOld authJalOff
      (authResidualFrame newSp ret F) :=
  ⟨authResidualFrame_pcFree newSp ret F hF, authJal_ret_even, authJal_target,
    by code_mem, hlen, hout⟩

/-- ⭐ A concrete EIP-7702 authorization: chain id 1, delegate `0xDD…DD`,
    nonce 0, `y_parity = 0`, `r = s = 1` — the shape of the set-code example in
    `SpecRef/Transactions.lean`. -/
def sampleAuth : Authorization :=
  { chainId := 1, address := List.replicate 20 (0xDD : BitVec 8), nonce := 0,
    yParity := 0, r := 1, s := 1 }

/-- The six-field wire layout in `authTupleFields` is not a guess: SpecRef's
    PUBLIC authorization decoder accepts it and round-trips to `sampleAuth`.
    (`RLP.Nat.toBytesBE` is well-founded recursion, so `decide`/`rfl` are stuck
    on concrete RLP; its equation lemmas do fire under `simp`.) -/
theorem sampleAuth_decodes :
    decodeItemAuthorization (.list (authTupleFields sampleAuth)) = .ok sampleAuth := by
  simp [decodeItemAuthorization, decodeItemScalar, decodeItemFixedBytes,
    authTupleFields, sampleAuth, RLP.Nat.toBytesBE, bytesBEtoNat,
    RLP.Nat.fromBytesBE]
  rfl

/-- ⭐ **Field-position pinning, concretely.** The 25-byte signing preimage with
    each field in its OWN byte range: MAGIC at `[0]`, the RLP list header at
    `[1]`, `chain_id` at `[2]`, the 20-byte `address` at `[3 … 23]` (`0x94`
    length byte then the address bytes), `nonce` at `[24]`.  Swapping
    `chain_id` and `address` changes these bytes, so the statement is not
    symmetric in them. -/
theorem sampleAuth_preimage :
    authSigningPreimage sampleAuth
      = [(0x05 : BitVec 8), 0xD7, 0x01, 0x94] ++ List.replicate 20 (0xDD : BitVec 8)
        ++ [(0x80 : BitVec 8)] := by
  simp [authSigningPreimage, sampleAuth, SET_CODE_TX_MAGIC, RLP.encode,
    RLP.encode.encodeItems, RLP.encodeBytes, RLP.Nat.toBytesBE]

theorem sampleAuth_preimage_length : (authSigningPreimage sampleAuth).length = 25 := by
  rw [sampleAuth_preimage]; simp

theorem sampleAuth_tuple_length : (authTupleRlp sampleAuth).length = 27 := by
  simp [authTupleRlp, authTupleFields, sampleAuth, RLP.encode,
    RLP.encode.encodeItems, RLP.encodeBytes, RLP.Nat.toBytesBE]

/-- ⭐ **Compiled satisfying instance**: the residual's computable half, fully
    instantiated at the real call site on `sampleAuth` with the concrete
    27-byte input length, a concrete zeroed 32-byte output buffer and an empty
    caller frame.  No prose claim — a closed term. -/
theorem authCallSite_ok_sample :
    tshCallSiteOk authCode authJalPC (BitVec.ofNat 64 27)
      (authTupleFields sampleAuth) (List.replicate 32 (0 : BitVec 8)) authJalOff
      (authResidualFrame (0x1000 : Word) (0x2000 : Word) empAssertion) :=
  authCallSite_ok _ _ _ _ _ _ pcFree_emp
    (by rw [show ((BitVec.ofNat 64 27 : Word)).toNat = 27 from by decide,
          ← authTupleRlp, sampleAuth_tuple_length])
    (by simp)

/-- The `halign` ABI obligation is satisfiable. -/
theorem sample_ret_align : (((0x2000 : Word)) &&& ~~~(1 : Word)) = (0x2000 : Word) := by
  decide

#print axioms eip7702_authorization_signing_hash_spec_within
#print axioms recover_authority_unfold
#print axioms eip7702AuthorizationSigningHash_prog_eq_frame
#print axioms authCallSite_ok_sample
#print axioms sampleAuth_preimage
#print axioms sampleAuth_decodes
#print axioms sampleAuth_tuple_length
#print axioms authSigningPreimage_segments
#print axioms authJal_target

end EvmAsm.Codegen.Eip7702AuthSigningHashSpec
