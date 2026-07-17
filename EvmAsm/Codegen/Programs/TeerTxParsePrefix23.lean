/-
  EvmAsm.Codegen.Programs.TeerTxParsePrefix23

  PASS 11 (continued) of the `tx_eip7702_existing_authority_refund` Fn.Spec.

  The **authorization-list walk segment** (`teerB + 440 → {2856, 676}`): the
  x21/x22 (callee-saved cursor/end) analogue of the `to`-walk segment
  (modules 17-20).  Structure:

      walkinit110(pin) ;; alglue0 ;;
        walknext116(pin) ;; alglue1 ;; … ;; walknext156(pin) ;; alglue9 ;;
        walknext161(pin) ;; authlist_setup

  The 10 `rlp_walk_next` cursor pins (sites 116/121/…/161) mirror the `to`-walk
  pins (module 19); the `alglue`-based segment-extension combinator
  `teer_alglue_extend` mirrors `teer_towalk_extend` (module 20) with x21/x22 as
  the snapshot cursor/end.  The final boundary `walknext161 ;; authlist_setup`
  stages the authorization-list content ptr/len (`x21 = a0 - a2`, `x22 = a2`)
  and materialises `&teer_auth_count` into `a2` for the count call — a clean
  frame-through join (the setup block touches no walk-callee scratch).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.TeerTxParsePrefix22

namespace EvmAsm.Codegen.TeerExistingAuthorityRefundSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The 10 authorization-list `rlp_walk_next` cursor pins (sites 116/…/161) -/

set_option maxRecDepth 8000 in
theorem teer_walknext116_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 464) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 472)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 468)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 464) (teerB + 472) (teerB + 468)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext116_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext121_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 484) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 492)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 488)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 484) (teerB + 492) (teerB + 488)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext121_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext126_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 504) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 512)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 508)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 504) (teerB + 512) (teerB + 508)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext126_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext131_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 524) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 532)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 528)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 524) (teerB + 532) (teerB + 528)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext131_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext136_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 544) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 552)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 548)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 544) (teerB + 552) (teerB + 548)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext136_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext141_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 564) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 572)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 568)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 564) (teerB + 572) (teerB + 568)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext141_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext146_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 584) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 592)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 588)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 584) (teerB + 592) (teerB + 588)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext146_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext151_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 604) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 612)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 608)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 604) (teerB + 612) (teerB + 608)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext151_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext156_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 624) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 632)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 628)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 624) (teerB + 632) (teerB + 628)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext156_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

set_option maxRecDepth 8000 in
theorem teer_walknext161_pin_spec (wn : RlpWalkNextAssumed fullCode)
    (hwn : wn.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_next)
    (srcBase endPtr a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (srcBytes : List (BitVec 8)) (srcOff : Nat)
    (halign : srcBase.toNat % 8 = 0) (hoff : srcOff < srcBytes.length)
    (hover : srcBase.toNat + srcOff < 2 ^ 64)
    (hvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 srcOff) = true)
    (C : Word)
    (hc : ∀ next len : Word,
      EvmAsm.Rv64.RLP.rlpItemDecode srcBytes srcOff
        (srcBase + BitVec.ofNat 64 srcOff) endPtr next len → next = C) :
    cpsBranchWithin ((1 + 87) + 1) (teerB + 644) fullCode
      ((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOff)) ** (.x11 ↦ᵣ endPtr) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion srcBase srcBytes))
      (teerB + 2856) teerFail (teerB + 652)
      (fun h => ∃ len : Word,
        ((.x1 ↦ᵣ (teerB + 648)) **
          (teerWalkScratch srcBase srcBytes **
           ((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len)))) h) :=
  teer_walknext_group_pin ((1 + 87) + 1) (teerB + 644) (teerB + 652) (teerB + 648)
    C endPtr (srcBase + BitVec.ofNat 64 srcOff) srcBytes srcOff
    _ (teerWalkScratch srcBase srcBytes) hc
    (teer_walknext161_group_spec wn hwn srcBase endPtr a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn srcBytes srcOff halign hoff hover hvalid)

/-! ## `rlp_walk_init`@110 group+pin ;; first auth-list glue (`teerB + 440 → {2856, 464}`) -/

set_option maxRecDepth 8000 in
/-- Composes the pinned `rlp_walk_init`@110 group with the first auth-list glue
    (`teer_alglue0_spec`, snapshot cursor `x21`/end `x22`), reaching the
    `rlp_walk_next`@116 CALL args at `teerB + 464`.  Mirrors
    `teer_walkinit54_toglue0_spec`. -/
theorem teer_walkinit110_alglue0_spec (wi : RlpWalkInitAssumed fullCode)
    (hwi : wi.entry = BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
    (listBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old raIn : Word)
    (v21o v22o : Word)
    (listBytes : List (BitVec 8)) (listOff : Nat)
    (halign : listBase.toNat % 8 = 0) (hoff : listOff < listBytes.length)
    (hover : listBase.toNat + listOff < 2 ^ 64)
    (hvalid : isValidByteAccess (listBase + BitVec.ofNat 64 listOff) = true)
    (C : Word)
    (hc1 : (listBase + BitVec.ofNat 64 listOff) + signExtend12 (1 : BitVec 12) = C)
    (hc2 : (listBase + BitVec.ofNat 64 listOff) +
        (((listBytes[listOff]'hoff).zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)) = C) :
    cpsBranchWithin (((1 + 81) + 1) + 4) (teerB + 440) fullCode
      (((.x1 ↦ᵣ raIn) **
        ((.x10 ↦ᵣ (listBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
          (.x12 ↦ᵣ a2Old) **
          (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
          (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion listBase listBytes)) **
        ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o)))
      (teerB + 2856) teerFail
      (teerB + 464)
      (((.x10 ↦ᵣ C) ** (.x11 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen)) **
          (.x21 ↦ᵣ C) ** (.x22 ↦ᵣ ((listBase + BitVec.ofNat 64 listOff) + listLen))) **
        ((.x1 ↦ᵣ (teerB + 444)) ** teerWalkScratch listBase listBytes **
          (.x12 ↦ᵣ (0 : Word)))) := by
  have h1 := cpsBranchWithin_frameR ((.x21 ↦ᵣ v21o) ** (.x22 ↦ᵣ v22o))
    (by repeat' first | exact pcFree_regIs | apply pcFree_sepConj)
    (teer_walkinit110_pin_spec wi hwi listBase listLen a2Old t0Old t1Old t2Old
      t3Old t4Old t5Old t6Old raIn listBytes listOff halign hoff hover hvalid C hc1 hc2)
  have h2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ (teerB + 444)) ** teerWalkScratch listBase listBytes ** (.x12 ↦ᵣ (0 : Word)))
    (by repeat' first
        | exact pcFree_regIs | exact teerWalkScratch_pcFree _ _ | apply pcFree_sepConj)
    (cpsTripleWithin_extend_code teer_mono
      (teer_alglue0_spec C ((listBase + BitVec.ofNat 64 listOff) + listLen) v21o v22o))
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    h1 (fun h hq => by xperm_hyp hq) h2 (fun h hq => to_teerFail _ h hq)

/-! ## One-step auth-list-walk segment extension combinator -/

set_option maxRecDepth 8000 in
/-- The x21/x22 analogue of `teer_towalk_extend`.  Chains an auth-list segment
    branch onto a `walknextNN ;; alglueK` block, threading `∃ len` into the next
    group's `x12`, adapting the scratch, and aligning the cursor. -/
theorem teer_alglue_extend
    {nPrev : Nat} {prevPC nextPC : Word}
    (Cprev Cnext endc raPrev nextMid : Word)
    (srcBase : Word) (srcBytes : List (BitVec 8)) (srcOffNext : Nat)
    (P : Assertion)
    (hoc : srcBase + BitVec.ofNat 64 srcOffNext = Cprev)
    (hprev : cpsBranchWithin nPrev (teerB + 440) fullCode P
      (teerB + 2856) teerFail prevPC
      (fun h => ∃ len : Word,
        (((.x10 ↦ᵣ Cprev) ** (.x11 ↦ᵣ endc) ** (.x21 ↦ᵣ Cprev) ** (.x22 ↦ᵣ endc)) **
          ((.x1 ↦ᵣ raPrev) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len))) h))
    (hnextAll : ∀ len t0 t1 t2 t3 t4 t5 t6 : Word,
      cpsBranchWithin (((1 + 87) + 1) + 3) prevPC fullCode
        (((.x1 ↦ᵣ raPrev) **
          ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOffNext)) ** (.x11 ↦ᵣ endc) **
            (.x12 ↦ᵣ len) **
            (.x5 ↦ᵣ t0) ** (.x6 ↦ᵣ t1) ** (.x7 ↦ᵣ t2) ** (.x28 ↦ᵣ t3) **
            (.x29 ↦ᵣ t4) ** (.x30 ↦ᵣ t5) ** (.x31 ↦ᵣ t6) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion srcBase srcBytes)) **
          ((.x21 ↦ᵣ Cprev) ** (.x22 ↦ᵣ endc)))
        (teerB + 2856) teerFail nextPC
        (fun h => ∃ len' : Word,
          (((.x10 ↦ᵣ Cnext) ** (.x11 ↦ᵣ endc) ** (.x21 ↦ᵣ Cnext) ** (.x22 ↦ᵣ endc)) **
            ((.x1 ↦ᵣ nextMid) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len'))) h)) :
    cpsBranchWithin (nPrev + (((1 + 87) + 1) + 3)) (teerB + 440) fullCode P
      (teerB + 2856) teerFail nextPC
      (fun h => ∃ len' : Word,
        (((.x10 ↦ᵣ Cnext) ** (.x11 ↦ᵣ endc) ** (.x21 ↦ᵣ Cnext) ** (.x22 ↦ᵣ endc)) **
          ((.x1 ↦ᵣ nextMid) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len'))) h) := by
  have hB : ∀ len : Word,
      cpsBranchWithin (((1 + 87) + 1) + 3) prevPC fullCode
        (((.x1 ↦ᵣ raPrev) **
          ((.x10 ↦ᵣ (srcBase + BitVec.ofNat 64 srcOffNext)) ** (.x11 ↦ᵣ endc) **
            (.x12 ↦ᵣ len) ** teerWalkScratch srcBase srcBytes)) **
          ((.x21 ↦ᵣ Cprev) ** (.x22 ↦ᵣ endc)))
        (teerB + 2856) teerFail nextPC
        (fun h => ∃ len' : Word,
          (((.x10 ↦ᵣ Cnext) ** (.x11 ↦ᵣ endc) ** (.x21 ↦ᵣ Cnext) ** (.x22 ↦ᵣ endc)) **
            ((.x1 ↦ᵣ nextMid) ** teerWalkScratch srcBase srcBytes ** (.x12 ↦ᵣ len'))) h) := by
    intro len
    exact teer_walk_scratch_regOwn_adaptor raPrev
      (srcBase + BitVec.ofNat 64 srcOffNext) endc len srcBase srcBytes
      ((.x21 ↦ᵣ Cprev) ** (.x22 ↦ᵣ endc))
      (fun t0 t1 t2 t3 t4 t5 t6 => hnextAll len t0 t1 t2 t3 t4 t5 t6)
  exact cpsBranchWithin_seq_cpsBranchWithin_with_perm_same_cr hprev
    (fun h hq => by
      obtain ⟨len, hbody⟩ := hq
      exact ⟨len, by rw [hoc]; xperm_hyp hbody⟩)
    (cpsBranchWithin_exists_pre hB)
    (fun h hq => to_teerFail _ h hq) (fun h hq => to_teerFail _ h hq)

end EvmAsm.Codegen.TeerExistingAuthorityRefundSpec
