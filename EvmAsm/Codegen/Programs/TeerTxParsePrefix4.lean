/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix4

  PASS 3 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The per-site `rlp_walk_next` CALL groups of the tx-parse prefix, each a thin
  instantiation of the site-abstract `teer_walknext_call_spec_at` (from
  `TeerTxParsePrefix2`) at its concrete call PC / `jal` offset:

    * `to`/value walk GROUP: sites 65 / 70 / 75 / 80 / 85 (walking to the `to`
      field) and 97 (advancing past `to` to `value`);
    * authorization-list walk GROUP: sites 116 / 121 / 126 / 131 / 136 / 141 /
      146 / 151 / 156 / 161 (descending to the authorization_list field).

  Each lifts the assumed `RlpWalkNextAssumed` contract through one `jal` via
  `callWithin_spec`, framing the callee's `t0..t6` scratch footprint; the
  advance result (`rlpWalkNextOk` success ∨ non-advance status) is carried
  through unchanged for the following `bne a1, 0` dispatch (in
  `TeerTxParsePrefix3`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix3

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-- **`rlp_walk_next`@65** (`teerB + 260 → teerB + 264`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff65 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 260)

set_option maxRecDepth 8000 in
theorem teer_walknext65_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 260) (teerB + 264) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 264)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 260) (.JAL .x1 wnJalOff65) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 260) teerProg 65 (.JAL .x1 wnJalOff65)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 260) wnJalOff65
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 260) + 4 = teerB + 264 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@70** (`teerB + 280 → teerB + 284`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff70 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 280)

set_option maxRecDepth 8000 in
theorem teer_walknext70_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 280) (teerB + 284) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 284)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 280) (.JAL .x1 wnJalOff70) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 280) teerProg 70 (.JAL .x1 wnJalOff70)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 280) wnJalOff70
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 280) + 4 = teerB + 284 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@75** (`teerB + 300 → teerB + 304`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff75 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 300)

set_option maxRecDepth 8000 in
theorem teer_walknext75_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 300) (teerB + 304) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 304)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 300) (.JAL .x1 wnJalOff75) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 300) teerProg 75 (.JAL .x1 wnJalOff75)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 300) wnJalOff75
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 300) + 4 = teerB + 304 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@80** (`teerB + 320 → teerB + 324`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff80 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 320)

set_option maxRecDepth 8000 in
theorem teer_walknext80_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 320) (teerB + 324) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 324)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 320) (.JAL .x1 wnJalOff80) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 320) teerProg 80 (.JAL .x1 wnJalOff80)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 320) wnJalOff80
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 320) + 4 = teerB + 324 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@85** (`teerB + 340 → teerB + 344`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff85 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 340)

set_option maxRecDepth 8000 in
theorem teer_walknext85_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 340) (teerB + 344) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 344)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 340) (.JAL .x1 wnJalOff85) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 340) teerProg 85 (.JAL .x1 wnJalOff85)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 340) wnJalOff85
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 340) + 4 = teerB + 344 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@97** (`teerB + 388 → teerB + 392`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff97 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 388)

set_option maxRecDepth 8000 in
theorem teer_walknext97_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 388) (teerB + 392) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 392)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 388) (.JAL .x1 wnJalOff97) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 388) teerProg 97 (.JAL .x1 wnJalOff97)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 388) wnJalOff97
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 388) + 4 = teerB + 392 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@116** (`teerB + 464 → teerB + 468`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff116 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 464)

set_option maxRecDepth 8000 in
theorem teer_walknext116_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 464) (teerB + 468) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 468)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 464) (.JAL .x1 wnJalOff116) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 464) teerProg 116 (.JAL .x1 wnJalOff116)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 464) wnJalOff116
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 464) + 4 = teerB + 468 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@121** (`teerB + 484 → teerB + 488`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff121 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 484)

set_option maxRecDepth 8000 in
theorem teer_walknext121_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 484) (teerB + 488) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 488)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 484) (.JAL .x1 wnJalOff121) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 484) teerProg 121 (.JAL .x1 wnJalOff121)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 484) wnJalOff121
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 484) + 4 = teerB + 488 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@126** (`teerB + 504 → teerB + 508`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff126 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 504)

set_option maxRecDepth 8000 in
theorem teer_walknext126_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 504) (teerB + 508) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 508)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 504) (.JAL .x1 wnJalOff126) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 504) teerProg 126 (.JAL .x1 wnJalOff126)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 504) wnJalOff126
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 504) + 4 = teerB + 508 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@131** (`teerB + 524 → teerB + 528`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff131 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 524)

set_option maxRecDepth 8000 in
theorem teer_walknext131_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 524) (teerB + 528) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 528)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 524) (.JAL .x1 wnJalOff131) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 524) teerProg 131 (.JAL .x1 wnJalOff131)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 524) wnJalOff131
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 524) + 4 = teerB + 528 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@136** (`teerB + 544 → teerB + 548`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff136 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 544)

set_option maxRecDepth 8000 in
theorem teer_walknext136_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 544) (teerB + 548) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 548)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 544) (.JAL .x1 wnJalOff136) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 544) teerProg 136 (.JAL .x1 wnJalOff136)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 544) wnJalOff136
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 544) + 4 = teerB + 548 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@141** (`teerB + 564 → teerB + 568`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff141 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 564)

set_option maxRecDepth 8000 in
theorem teer_walknext141_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 564) (teerB + 568) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 568)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 564) (.JAL .x1 wnJalOff141) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 564) teerProg 141 (.JAL .x1 wnJalOff141)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 564) wnJalOff141
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 564) + 4 = teerB + 568 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@146** (`teerB + 584 → teerB + 588`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff146 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 584)

set_option maxRecDepth 8000 in
theorem teer_walknext146_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 584) (teerB + 588) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 588)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 584) (.JAL .x1 wnJalOff146) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 584) teerProg 146 (.JAL .x1 wnJalOff146)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 584) wnJalOff146
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 584) + 4 = teerB + 588 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@151** (`teerB + 604 → teerB + 608`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff151 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 604)

set_option maxRecDepth 8000 in
theorem teer_walknext151_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 604) (teerB + 608) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 608)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 604) (.JAL .x1 wnJalOff151) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 604) teerProg 151 (.JAL .x1 wnJalOff151)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 604) wnJalOff151
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 604) + 4 = teerB + 608 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@156** (`teerB + 624 → teerB + 628`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff156 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 624)

set_option maxRecDepth 8000 in
theorem teer_walknext156_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 624) (teerB + 628) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 628)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 624) (.JAL .x1 wnJalOff156) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 624) teerProg 156 (.JAL .x1 wnJalOff156)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 624) wnJalOff156
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 624) + 4 = teerB + 628 from by bv_omega] at hres
  exact hres

/-- **`rlp_walk_next`@161** (`teerB + 644 → teerB + 648`).  Thin instantiation of
    `teer_walknext_call_spec_at`. -/
abbrev wnJalOff161 : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_next (GuestAddrs.tx_eip7702_existing_authority_refund + 644)

set_option maxRecDepth 8000 in
theorem teer_walknext161_call_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true) :
    cpsTripleWithin (1 + 87) (teerB + 644) (teerB + 648) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      ((.x1 ↦ᵣ (teerB + 648)) **
        ((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes) **
         (fun h =>
           EvmAsm.Rv64.RLP.rlpWalkNextOk (srcBase + BitVec.ofNat 64 srcOff) endPtr
             srcBytes srcOff h ∨
           (∃ st : Word,
             (((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ st) **
                (.x12 ↦ᵣ (0 : Word)) ** ⌜st ≠ (0 : Word)⌝) h))))) := by
  have hmem : ∀ a i, CodeReq.singleton (teerB + 644) (.JAL .x1 wnJalOff161) a = some i →
      fullCode a = some i := fun a i h =>
    teer_mono a i
      (CodeReq.ofProg_mem_at teerB (teerB + 644) teerProg 161 (.JAL .x1 wnJalOff161)
        (by bv_omega) (by rw [teer_length]; decide) (by decide)
        (by rw [teer_length]; decide) a i h)
  have hres := teer_walknext_call_spec_at wn (teerB + 644) wnJalOff161
    (by rw [hwn]; decide) hmem (by decide)
    srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn srcBytes srcOff
    halign hoff hover hvalid
  rw [show (teerB + 644) + 4 = teerB + 648 from by bv_omega] at hres
  exact hres


end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
