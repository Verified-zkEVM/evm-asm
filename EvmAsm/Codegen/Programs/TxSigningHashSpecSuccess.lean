/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecSuccess

  Success-path phase glue for K145 `tx_signing_hash` Spec (#12038); multi-rate segments.

  Composes already-proved body slices toward the nonempty short-list path
  (hdr → nth → prefix → kss). Empty-len fail lives in BodyLate / Spec.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecBodyLate

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashResidual
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef
open EvmAsm.Rv64.Tactics

/-! ## Setup → nonempty fallthrough (`H+36 → H+72`) -/

/-- Nonempty `len` (`a1 ≠ 0`) after setup + type-prefix store. -/
theorem tshSetupThenNonempty_spec
    (a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20 wordOld : Word)
    (halign : alignToDword TshBuf = TshBuf)
    (hvalid : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0) :
    cpsTripleWithin (5 + 3 + 1) (H + 36) (H + 72) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
  have hsetup := tshSetupThroughSb_spec a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20
    wordOld halign hvalid
  have hsetupF := cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcf) hsetup
  have hsetupW : cpsTripleWithin (5 + 3) (H + 36) (H + 68) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hsetupF
  have hnt := tshEmptyLenBeq_ntaken a1 hlen
  have hntF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
      (.x14 ↦ᵣ a4) **
      (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
      (.x20 ↦ᵣ a4) **
      (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
    (by pcf) hnt
  have hntW : cpsTripleWithin 1 (H + 68) (H + 72) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) **
        (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hntF
  exact cpsTripleWithin_seq_same_cr hsetupW hntW

/-! ## Setup → short-list header (`H+36 → H+108`)

    Nonempty length + short RLP list header (`0xc0 ≤ hdr < 0xf8`).
    Carries the input `bytesRegion` and leaves `s5 := 1`. -/

theorem tshSetupThroughHdrShort_spec
    (a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20 v21 wordOld : Word)
    (input : List (BitVec 8))
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word)) :
    cpsTripleWithin (5 + 3 + 1 + 7) (H + 36) (H + 108) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ tshHdrByte input h0) ** (.x6 ↦ᵣ (248 : Word)) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
        bytesRegion a0 input) := by
  have hne := tshSetupThenNonempty_spec a0 a1 a2 a3 a4 v5 v8 v9 v18 v19 v20
    wordOld halignBuf hvalidBuf hlen
  have hneF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x21 ↦ᵣ v21) ** bytesRegion a0 input)
    (by
      repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact bytesRegion_pcFree _ _) hne
  have hneW : cpsTripleWithin (5 + 3 + 1) (H + 36) (H + 72) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ v21) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
        bytesRegion a0 input) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hneF
  have hhdr := tshHdrParseShort_spec a0 TshBuf v6 v21 input h0
    halignIn hoverIn hvalidIn hge hult
  have hhdrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
      (.x14 ↦ᵣ a4) **
      (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) **
      (.x0 ↦ᵣ (0 : Word)) **
      (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))
    (by pcf) hhdr
  have hhdrW : cpsTripleWithin 7 (H + 72) (H + 108) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ v21) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
        bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ tshHdrByte input h0) ** (.x6 ↦ᵣ (248 : Word)) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
        bytesRegion a0 input) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hhdrF
  exact cpsTripleWithin_seq_same_cr hneW hhdrW

/-! ## Short-hdr → nth ABI setup (`H+108 → H+156`), `nFields ≠ 0`

    Leaves ABI args + scratch pointers ready for `tsh_nth_callWithin`. -/

abbrev tshNthIndexW (nFields : Word) : Word :=
  nFields + signExtend12 (-1 : BitVec 12)

/-- From post-short-hdr through pointer materialization. Requires `a2 ≠ 0`. -/
theorem tshNthSetupToJal_spec
    (inPtr lenW nFields typePrefix outPtr hdrByte v6 v10 v11 v12 v13 v14 v22 : Word)
    (hnz : nFields ≠ 0) :
    cpsTripleWithin (1 + 1 + 1 + 3 + 6) (H + 108) (H + 156) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ v22) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ tshNthIndexW nFields) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ tshNthIndexW nFields) **
        (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hli := tshPayloadOffInit_spec v22
  have hliF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
      (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hli
  have hliW : cpsTripleWithin 1 (H + 108) (H + 112) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) ** (.x22 ↦ᵣ v22) **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hnt := tshNFieldsBeq_ntaken nFields hnz
  have hntF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) **
      (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
      (.x22 ↦ᵣ (0 : Word)))
    (by pcf) hnt
  have hntW : cpsTripleWithin 1 (H + 112) (H + 116) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hntF
  have c01 := cpsTripleWithin_seq_same_cr hliW hntW
  have hidx := tshNthIndex_spec nFields hdrByte
  have hidxF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) **
      (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
      (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
      (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hidx
  have hidxW : cpsTripleWithin 1 (H + 116) (H + 120) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ hdrByte) ** (.x6 ↦ᵣ v6) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
        (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ tshNthIndexW nFields) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hidxF
  have c012 := cpsTripleWithin_seq_same_cr c01 hidxW
  have hmv := tshNthArgMoves_spec inPtr lenW (tshNthIndexW nFields) v10 v11 v12
  have hmvF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ nFields) ** (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
      (.x6 ↦ᵣ v6) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
      (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hmv
  have hmvW : cpsTripleWithin 3 (H + 120) (H + 132) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ tshNthIndexW nFields) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ tshNthIndexW nFields) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ tshNthIndexW nFields) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hmvF
  have c0123 := cpsTripleWithin_seq_same_cr c012 hmvW
  have hptr := tshNthPtrs_spec v13 v14
  have hptrF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
      (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ tshNthIndexW nFields) ** (.x6 ↦ᵣ v6) **
      (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ tshNthIndexW nFields) **
      (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
    (by pcf) hptr
  have hptrW : cpsTripleWithin 6 (H + 132) (H + 156) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ tshNthIndexW nFields) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ tshNthIndexW nFields) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ nFields) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x5 ↦ᵣ tshNthIndexW nFields) ** (.x6 ↦ᵣ v6) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ tshNthIndexW nFields) **
        (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hptrF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr c0123 hptrW)

/-! ## Glue: setup → short-hdr → nth ABI setup (`H+36 → H+156`) -/

/-- Nonempty short-list path through nth pointer materialization (`nFields ≠ 0`). -/
theorem tshSetupThroughNthSetup_spec
    (a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20 v21 v22 wordOld : Word)
    (input : List (BitVec 8))
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (hnz : a2 ≠ 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word)) :
    cpsTripleWithin (5 + 3 + 1 + 7 + (1 + 1 + 1 + 3 + 6)) (H + 36) (H + 156) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ v22) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input)
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
        (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
        (.x5 ↦ᵣ tshNthIndexW a2) ** (.x6 ↦ᵣ (248 : Word)) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) ** (.x22 ↦ᵣ (0 : Word)) **
        (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
        bytesRegion a0 input) := by
  let F : Assertion :=
    (.x21 ↦ᵣ (1 : Word)) **
      (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
      bytesRegion a0 input
  have hF : F.pcFree := by
    unfold F
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
  have hhdr := tshSetupThroughHdrShort_spec a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20
    v21 wordOld input halignBuf hvalidBuf hlen h0
    halignIn hoverIn hvalidIn hge hult
  have hhdrF := cpsTripleWithin_frameR (.x22 ↦ᵣ v22) (by pcf) hhdr
  have hn := tshNthSetupToJal_spec a0 a1 a2 a3 a4 (tshHdrByte input h0)
    (248 : Word) a0 a1 a2 a3 a4 v22 hnz
  have hnF := cpsTripleWithin_frameR F hF hn
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      -- mid: hdr post ** x22  →  nth pre ** F
      simp only [F] at hp ⊢
      xperm_hyp hp) hhdrF hnF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [F] at hq
      xperm_hyp hq) c

/-! ## Post-nth success continue → prefix jal site (`H+160 → H+216`)

    Assumes nth returned `a0 = 0`. Loads scratch off/len, computes
    `payloadLen`, materializes prefix out/cell pointers. -/

/-- nth-success fallthrough through prefix ABI setup. -/
theorem tshPostNthToPrefixJal_spec
    (v5 v6 v7 v11 v12 v22 offVal lenVal hdrLen : Word) :
    cpsTripleWithin (1 + 8 + 6) (H + 160) (H + 216) fullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal))
      ((.x10 ↦ᵣ ((offVal + lenVal) - hdrLen)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
        (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ ((offVal + lenVal) - hdrLen)) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal)) := by
  have hbr := tshNthFail_ntaken (0 : Word) rfl
  have hbrF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal))
    (by pcf) hbr
  have hpay := tshPayloadLen_spec v5 v6 v7 (0 : Word) v22 offVal lenVal hdrLen
  have hpayF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
    (by pcf) hpay
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hbrF hpayF
  have hptr := tshPrefixPtrs_spec v11 v12
  have hptrF := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ ((offVal + lenVal) - hdrLen)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ TshBuf) ** (.x6 ↦ᵣ (offVal + lenVal)) ** (.x7 ↦ᵣ lenVal) **
      (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ ((offVal + lenVal) - hdrLen)) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal))
    (by pcf) hptr
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hptrF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

/-! ## Post-nth → short prefix `callWithin` (`H+160 → H+220`) -/

/-- nth-success continue through short `rlp_encode_list_prefix` call. -/
theorem tshPostNthThenPrefixCall_spec
    (vOld v5 v6 v7 v11 v12 v22 offVal lenVal hdrLen cellOld : Word)
    (outBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (h_len : ((offVal + lenVal) - hdrLen).toNat < 56)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    let payloadLen := (offVal + lenVal) - hdrLen
    cpsTripleWithin ((1 + 8 + 6) + (1 + 8)) (H + 160) (tshPrefixJalPC + 4) fullCode
      ((.x1 ↦ᵣ vOld) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F)
      ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr
          (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + payloadLen.toNat))) **
        (tshPrefixCellPtr ↦ₘ (1 : Word)) ** F) := by
  intro payloadLen
  have hAmb :
      ((.x1 ↦ᵣ vOld) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact bytesRegion_pcFree _ _
      | exact hF
  have hprep := tshPostNthToPrefixJal_spec v5 v6 v7 v11 v12 v22 offVal lenVal hdrLen
  have hprepF := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ vOld) **
      bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F)
    hAmb hprep
  have hCallF :
      ((.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) ** F).pcFree := by
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact hF
  have hcall := tsh_prefix_short_callWithin vOld payloadLen tshPrefixOutPtr
    tshPrefixCellPtr TshBuf (offVal + lenVal) lenVal outBytes cellOld
    ((.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
      (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) ** F)
    hCallF h_len h_out_align h_out_len h_out_valid
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [payloadLen] at hp ⊢
      xperm_hyp hp) hprepF hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [payloadLen] at hq ⊢
      xperm_hyp hq) c

/-! ## Setup → nth `callWithin` (`H+36 → H+160`)

    Frames the K20 call ambient through `tshSetupThroughNthSetup_spec`,
    weakens scratch temps to `regOwn`, then applies `tsh_nth_callWithin`. -/

open EvmAsm.Codegen.RlpListNthItemSAsm

/-- Ambient owned by the caller across the nth JAL (not touched by setup). -/
abbrev tshNthCallAmbient (sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen : Word) :
    Assertion :=
  (.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
    (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
    (.x31 ↦ᵣ v31) **
    (tshNthOffPtr ↦ₘ oldOff) ** (tshNthLenPtr ↦ₘ oldLen)

theorem tshNthCallAmbient_pcFree
    (sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen : Word) :
    (tshNthCallAmbient sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen).pcFree := by
  unfold tshNthCallAmbient
  pcf

/-- Post-setup frame carried through the nth call (caller-owned). -/
abbrev tshNthCallFrame (v22 wordBuf a3 : Word) : Assertion :=
  (.x22 ↦ᵣ v22) **
    (TshBuf ↦ₘ replaceByte wordBuf (byteOffset TshBuf) (a3.truncate 8))

theorem tshNthCallFrame_pcFree (v22 wordBuf a3 : Word) :
    (tshNthCallFrame v22 wordBuf a3).pcFree := by
  unfold tshNthCallFrame
  pcf

/-- Saved s-regs at the nth jal site after short-hdr setup (`s5 = 1`). -/
def tshNthSaved (ra inPtr lenW nFields typePrefix outPtr : Word) : Saved where
  ra := ra
  s0 := inPtr
  s1 := lenW
  s2 := nFields
  s3 := typePrefix
  s4 := outPtr
  s5 := 1

/-- Mid-state after `tshSetupThroughNthSetup` plus call ambient (regIs temps). -/
abbrev tshNthJalMid
    (a0 a1 a2 a3 a4 v5 v6 v22 wordOld : Word)
    (sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen : Word)
    (input : List (BitVec 8)) : Assertion :=
  ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
    (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
    (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
    (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
    (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) ** (.x22 ↦ᵣ v22) **
    (.x0 ↦ᵣ (0 : Word)) **
    (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)) **
    bytesRegion a0 input **
    tshNthCallAmbient sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen)

/-- CallWithin pre at the nth jal (regOwn temps + frame). -/
abbrev tshNthJalCallPre
    (a0 a1 a2 a3 a4 vOld sp0 oldOff oldLen wordOld : Word)
    (input : List (BitVec 8)) : Assertion :=
  ((.x1 ↦ᵣ vOld) **
    callEntryRest sp0 a0 a1 (tshNthIndexW a2) tshNthOffPtr tshNthLenPtr
      oldOff oldLen (tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4) input) **
  tshNthCallFrame (0 : Word) wordOld a3

/-- Reshape setup-mid (regIs) into nth callWithin pre (regOwn). -/
theorem tshNthJalMid_to_callPre
    (a0 a1 a2 a3 a4 wordOld : Word)
    (sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen : Word)
    (input : List (BitVec 8))
    (h : PartialState)
    (hp : tshNthJalMid a0 a1 a2 a3 a4 (tshNthIndexW a2) (248 : Word) (0 : Word)
      wordOld sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen input h) :
    tshNthJalCallPre a0 a1 a2 a3 a4 vOld sp0 oldOff oldLen wordOld input h := by
  simp only [tshNthJalMid, tshNthJalCallPre, tshNthCallAmbient, tshNthCallFrame,
    callEntryRest, savedRegTail, entryRest, tshNthSaved] at hp ⊢
  -- Order atoms to match callEntryRest, still as regIs on temps.
  have hpOrd :
      (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
        (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
        (.x5 ↦ᵣ tshNthIndexW a2) ** (.x6 ↦ᵣ (248 : Word)) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
        (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
        (tshNthLenPtr ↦ₘ oldLen)) **
      ((.x22 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))) h := by
    xperm_hyp hp
  -- Left-assoc peel: move each temp to the left, own it, continue.
  have step5 :
      ((.x5 ↦ᵣ tshNthIndexW a2) **
        (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
          (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
          (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
          (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
          (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
          (.x6 ↦ᵣ (248 : Word)) **
          (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
          (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
          bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
          (tshNthLenPtr ↦ₘ oldLen)) **
        ((.x22 ↦ᵣ (0 : Word)) **
          (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8))))) h := by
    xperm_hyp hpOrd
  have own5 := sepConj_mono_left (regIs_to_regOwn .x5 (tshNthIndexW a2)) h step5
  have step6 :
      ((.x6 ↦ᵣ (248 : Word)) **
        (regOwn .x5 **
          (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
            (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
            (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
            (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
            (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
            (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
            (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
            (tshNthLenPtr ↦ₘ oldLen)) **
          ((.x22 ↦ᵣ (0 : Word)) **
            (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))))) h := by
    xperm_hyp own5
  have own6 := sepConj_mono_left (regIs_to_regOwn .x6 (248 : Word)) h step6
  have step7 :
      ((.x7 ↦ᵣ v7) **
        (regOwn .x6 ** regOwn .x5 **
          (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
            (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
            (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
            (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
            (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
            (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
            (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
            (tshNthLenPtr ↦ₘ oldLen)) **
          ((.x22 ↦ᵣ (0 : Word)) **
            (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))))) h := by
    xperm_hyp own6
  have own7 := sepConj_mono_left (regIs_to_regOwn .x7 v7) h step7
  have step28 :
      ((.x28 ↦ᵣ v28) **
        (regOwn .x7 ** regOwn .x6 ** regOwn .x5 **
          (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
            (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
            (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
            (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
            (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
            (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) **
            (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
            (tshNthLenPtr ↦ₘ oldLen)) **
          ((.x22 ↦ᵣ (0 : Word)) **
            (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))))) h := by
    xperm_hyp own7
  have own28 := sepConj_mono_left (regIs_to_regOwn .x28 v28) h step28
  have step29 :
      ((.x29 ↦ᵣ v29) **
        (regOwn .x28 ** regOwn .x7 ** regOwn .x6 ** regOwn .x5 **
          (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
            (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
            (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
            (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
            (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
            (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
            (tshNthLenPtr ↦ₘ oldLen)) **
          ((.x22 ↦ᵣ (0 : Word)) **
            (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))))) h := by
    xperm_hyp own28
  have own29 := sepConj_mono_left (regIs_to_regOwn .x29 v29) h step29
  have step30 :
      ((.x30 ↦ᵣ v30) **
        (regOwn .x29 ** regOwn .x28 ** regOwn .x7 ** regOwn .x6 ** regOwn .x5 **
          (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
            (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
            (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
            (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
            (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
            (.x31 ↦ᵣ v31) ** (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
            (tshNthLenPtr ↦ₘ oldLen)) **
          ((.x22 ↦ᵣ (0 : Word)) **
            (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))))) h := by
    xperm_hyp own29
  have own30 := sepConj_mono_left (regIs_to_regOwn .x30 v30) h step30
  have step31 :
      ((.x31 ↦ᵣ v31) **
        (regOwn .x30 ** regOwn .x29 ** regOwn .x28 ** regOwn .x7 **
          regOwn .x6 ** regOwn .x5 **
          (((.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
            (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
            (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ (1 : Word)) **
            (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ tshNthIndexW a2) **
            (.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr) **
            (.x0 ↦ᵣ (0 : Word)) **
            bytesRegion a0 input ** (tshNthOffPtr ↦ₘ oldOff) **
            (tshNthLenPtr ↦ₘ oldLen)) **
          ((.x22 ↦ᵣ (0 : Word)) **
            (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf) (a3.truncate 8)))))) h := by
    xperm_hyp own30
  have own31 := sepConj_mono_left (regIs_to_regOwn .x31 v31) h step31
  xperm_hyp own31

/-- Setup through nth ABI + `rlp_list_nth_item` callWithin. `H+36 → H+160`. -/
theorem tshSetupThroughNthCall_spec
    (a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19 v20 v21 wordOld : Word)
    (sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen : Word)
    (input : List (BitVec 8)) (listLen index : Nat)
    (halignBuf : alignToDword TshBuf = TshBuf)
    (hvalidBuf : isValidByteAccess TshBuf = true)
    (hlen : a1 ≠ 0)
    (hnz : a2 ≠ 0)
    (h0 : 0 < input.length)
    (halignIn : a0.toNat % 8 = 0)
    (hoverIn : a0.toNat < 2 ^ 64)
    (hvalidIn : isValidByteAccess a0 = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word))
    (hlistLenW : a1 = BitVec.ofNat 64 listLen)
    (hindexW : tshNthIndexW a2 = BitVec.ofNat 64 index)
    (hindex : index < 2 ^ 64)
    (hslack : listLen + 9 ≤ input.length)
    (hover : a0.toNat + input.length < 2 ^ 64)
    (hvalidBytes : ∀ k, k < input.length →
      isValidByteAccess (a0 + BitVec.ofNat 64 k) = true) :
    let setupFuel := 5 + 3 + 1 + 7 + (1 + 1 + 1 + 3 + 6)
    let callFuel := 1 + ((12 + ((85 + 93 * (index + 2)) + 6)) + 9)
    let saved := tshNthSaved (tshNthJalPC + 4) a0 a1 a2 a3 a4
    cpsTripleWithin (setupFuel + callFuel) (H + 36) (tshNthJalPC + 4) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) **
        (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (TshBuf ↦ₘ wordOld) ** bytesRegion a0 input **
        tshNthCallAmbient sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen)
      (((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        callReturnResult sp0 a0 (tshNthIndexW a2) tshNthOffPtr tshNthLenPtr
          oldOff oldLen saved input listLen index) **
        tshNthCallFrame (0 : Word) wordOld a3) := by
  intro setupFuel callFuel saved
  have hsetup := tshSetupThroughNthSetup_spec a0 a1 a2 a3 a4 v5 v6 v8 v9 v18 v19
    v20 v21 (0 : Word) wordOld input halignBuf hvalidBuf hlen hnz h0
    halignIn hoverIn hvalidIn hge hult
  have hAmb := tshNthCallAmbient_pcFree sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen
  have hsetupF := cpsTripleWithin_frameR
    (tshNthCallAmbient sp0 vOld v7 v28 v29 v30 v31 oldOff oldLen) hAmb hsetup
  have hcall := tsh_nth_callWithin vOld sp0 a0 a1 (tshNthIndexW a2) oldOff oldLen
    (tshNthSaved vOld a0 a1 a2 a3 a4) input listLen index
    (tshNthCallFrame (0 : Word) wordOld a3)
    (tshNthCallFrame_pcFree _ _ _)
    hlistLenW hindexW hindex halignIn hslack hover hvalidBytes
  have c := cpsTripleWithin_seq_perm_same_cr (fun h hp =>
    tshNthJalMid_to_callPre a0 a1 a2 a3 a4 wordOld sp0 vOld v7 v28 v29 v30 v31
      oldOff oldLen input h (by
        simp only [tshNthJalMid, tshNthCallAmbient] at hp ⊢
        xperm_hyp hp)) hsetupF hcall
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [tshNthCallAmbient] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [saved, tshNthSaved] at hq ⊢
      exact hq) c

/-! ## Post-prefix typed gather → kss jal site (`H+220 → H+316`)

    Short-list / typed (`typePrefix ≠ 0`) path: reload cell, materialize
    segs base, fill three segment descriptors, set kss ABI args. -/

/-- Typed path through segment-table fill and kss arg setup.

    `x10`/`x11`/`x12` are overwritten by `tshKssArgSetup`; entry values are
    unconstrained (prefix call leaves them as out/cell pointers). -/
theorem tshPostPrefixTypedToKssJal_spec
    (v5 v29 v30 v31 typePrefix inPtr outPtr hdrLen payloadLen cellVal : Word)
    (v10 v11 v12 old0 old1 old2 old3 old4 old5 : Word)
    (hnz : typePrefix ≠ 0) :
    cpsTripleWithin (6 + 3 + 4 + 5 + 3 + 3) (H + 220) (H + 316) fullCode
      ((.x5 ↦ᵣ v5) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (tshPrefixCellPtr ↦ₘ cellVal) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
      ((.x5 ↦ᵣ (1 : Word)) ** (.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
        (.x31 ↦ᵣ (inPtr + hdrLen)) **
        (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ tshSegsBase) ** (.x11 ↦ᵣ (3 : Word)) ** (.x12 ↦ᵣ outPtr) **
        (tshPrefixCellPtr ↦ₘ cellVal) **
        (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ (1 : Word)) **
        ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ cellVal) **
        ((tshSegsBase + 32) ↦ₘ (inPtr + hdrLen)) **
        ((tshSegsBase + 40) ↦ₘ payloadLen)) := by
  -- H+220 → H+244: cell + segs base
  have hprep := tshPostPrefixSegsPrep_spec v5 v29 v30 cellVal
  have hprepF := cpsTripleWithin_frameR
    ((.x31 ↦ᵣ v31) ** (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ typePrefix) **
      (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) **
      (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
      ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
      ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
    (by pcf) hprep
  -- H+244 → H+256: typed typeLen := 1
  have hty := tshTypeLenTyped_spec typePrefix TshBuf hnz
  have htyF := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) ** (.x31 ↦ᵣ v31) **
      (.x8 ↦ᵣ inPtr) ** (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ hdrLen) **
      (.x22 ↦ᵣ payloadLen) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) **
      (tshPrefixCellPtr ↦ₘ cellVal) **
      (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
      ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
      ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
    (by pcf) hty
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hprepF htyF
  -- H+256 → H+272: seg0
  have hs0 := tshSeg0Fill_spec v31 (1 : Word) old0 old1
  have hs0F := cpsTripleWithin_frameR
    ((.x29 ↦ᵣ cellVal) ** (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ typePrefix) **
      (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) **
      (tshPrefixCellPtr ↦ₘ cellVal) **
      ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
      ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
    (by pcf) hs0
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hs0F
  -- H+272 → H+292: seg1
  have hs1 := tshSeg1Fill_spec TshBuf cellVal old2 old3
  have hs1F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (1 : Word)) ** (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ typePrefix) **
      (.x20 ↦ᵣ outPtr) ** (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
      (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
      (.x12 ↦ᵣ v12) **
      (tshPrefixCellPtr ↦ₘ cellVal) **
      (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ (1 : Word)) **
      ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5))
    (by pcf) hs1
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c012 hs1F
  -- H+292 → H+304: seg2
  have hs2 := tshSeg2Fill_spec inPtr hdrLen payloadLen tshPrefixOutPtr old4 old5
  have hs2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (1 : Word)) ** (.x29 ↦ᵣ cellVal) ** (.x19 ↦ᵣ typePrefix) **
      (.x20 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
      (tshPrefixCellPtr ↦ₘ cellVal) **
      (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ (1 : Word)) **
      ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ cellVal))
    (by pcf) hs2
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c0123 hs2F
  -- H+304 → H+316: kss ABI args
  have harg := tshKssArgSetup_spec outPtr v10 v11 v12
  have hargF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (1 : Word)) ** (.x29 ↦ᵣ cellVal) ** (.x31 ↦ᵣ (inPtr + hdrLen)) **
      (.x8 ↦ᵣ inPtr) ** (.x19 ↦ᵣ typePrefix) ** (.x21 ↦ᵣ hdrLen) **
      (.x22 ↦ᵣ payloadLen) ** (.x0 ↦ᵣ (0 : Word)) **
      (tshPrefixCellPtr ↦ₘ cellVal) **
      (tshSegsBase ↦ₘ TshBuf) ** ((tshSegsBase + 8) ↦ₘ (1 : Word)) **
      ((tshSegsBase + 16) ↦ₘ tshPrefixOutPtr) ** ((tshSegsBase + 24) ↦ₘ cellVal) **
      ((tshSegsBase + 32) ↦ₘ (inPtr + hdrLen)) **
      ((tshSegsBase + 40) ↦ₘ payloadLen))
    (by pcf) harg
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01234 hargF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

/-! ## Kss short callWithin → success status (`H+316 → bodyExit`) -/

/-- Short-domain segments call then `li a0,0; jal` skip-fail.

    Kss already returns `a0 = 0`; the success reconverge re-writes `a0` and
    skips the fail `li`. -/
theorem tshKssCallThenSuccess_spec
    (vOld sp0 segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let ret := tshKssJalPC + 4
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let fuel := 19 + kssBodyFuelMulti segs
    cpsTripleWithin ((1 + fuel) + 2) tshKssJalPC tshBodyExit fullCode
      (((.x1 ↦ᵣ vOld) **
        (tshKssCallPre sp0 newSp segsBase outputBase segs os
          v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A ** F)))
      (((.x1 ↦ᵣ ret) **
        (tshKssCallPost sp0 newSp ret segsBase outputBase segs
          v8 v9 v18 v19 v20 v21 v22 A ** F))) := by
  intro ret newSp fuel
  have hcall := tsh_kss_callWithin vOld sp0 segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A F hA hF hos hcount hsegs
  -- Rest of the kss post besides a0 (which success status owns).
  let Rest : Assertion :=
    (.x1 ↦ᵣ ret) **
      ((.x2 ↦ᵣ sp0) ** tshKssSregs v8 v9 v18 v19 v20 v21 v22 **
        frameSlotsSaved kssFrame newSp (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
        ((regOwn .x11) ** (regOwn .x12) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          regOwns kssFreeTemps **
          bytesRegion KssZk3
            (kssFinalState
              (kssAbsorbed (kssMsg segs) (kssMsg segs).length)
              (kssFill (kssMsg segs).length)) **
          bytesRegion outputBase (Stateless.SpecRef.keccak256 (kssMsg segs)) **
          kssSegsIs segsBase segs ** A ** F))
  have hRest : Rest.pcFree := by
    unfold Rest
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj (tshKssSregs_pcFree _ _ _ _ _ _ _) ?_
    refine pcFree_sepConj
      (pcFree_frameSlotsSaved kssFrame newSp
        (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22)) ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regIs ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj pcFree_regOwn ?_
    refine pcFree_sepConj (by pcf) ?_  -- regOwns kssFreeTemps
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (bytesRegion_pcFree _ _) ?_
    refine pcFree_sepConj (kssSegsIs_pcFree segsBase segs) ?_
    exact pcFree_sepConj hA hF
  have hsucc := tshSuccessStatus_spec (0 : Word)
  have hsuccF := cpsTripleWithin_frameR Rest hRest hsucc
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [Rest, tshKssCallPost, kssCallerPost_multi] at hp ⊢
      xperm_hyp hp) hcall hsuccF
  exact cpsTripleWithin_weaken (fun _ hp => hp)
    (fun _ hq => by
      simp only [Rest, tshKssCallPost, kssCallerPost_multi] at hq ⊢
      xperm_hyp hq) c

/-! ## Typed gather → kss call → success (`H+220 → bodyExit`)

    Frames kss call ambient through `tshPostPrefixTypedToKssJal_spec`, reshapes
    the written segment table + payload regions into `kssSegsIs`, then applies
    `tshKssCallThenSuccess_spec`. -/

/-- Three-segment gather matching the typed short-list fill. -/
abbrev tshTypedSegs (typeBs prefixBs payloadBs : List (BitVec 8))
    (inPtr hdrLen : Word) : List KssSeg :=
  [(TshBuf, typeBs), (tshPrefixOutPtr, prefixBs), (inPtr + hdrLen, payloadBs)]

/-- Typed gather through short kss + success status. -/
theorem tshTypedGatherThroughSuccess_spec
    (v5 v29 v30 v31 typePrefix inPtr outPtr hdrLen payloadLen cellVal : Word)
    (v10 v11 v12 old0 old1 old2 old3 old4 old5 : Word)
    (vOld sp0 v6 v7 v9 v18 : Word)
    (typeBs prefixBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hnz : typePrefix ≠ 0)
    (htypeLen : typeBs.length = 1)
    (hcell : cellVal = BitVec.ofNat 64 prefixBs.length)
    (hpayW : payloadLen = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ s ∈ tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen,
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let segs := tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let gatherFuel := 6 + 3 + 4 + 5 + 3 + 3
    let kssFuel := 1 + (19 + kssBodyFuelMulti segs) + 2
    cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
      ((.x5 ↦ᵣ v5) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        frameSlotsOwn kssFrame newSp **
        (tshPrefixCellPtr ↦ₘ cellVal) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
        bytesRegion TshBuf typeBs ** bytesRegion tshPrefixOutPtr prefixBs **
        bytesRegion (inPtr + hdrLen) payloadBs **
        bytesRegion KssZk3 os **
        bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
        regOwns kssFreeTemps ** A ** F)
      (((.x1 ↦ᵣ (tshKssJalPC + 4)) **
        (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
          inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
          ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
            (.x31 ↦ᵣ (inPtr + hdrLen)) **
            (tshPrefixCellPtr ↦ₘ cellVal) ** F)))) := by
  intro segs newSp gatherFuel kssFuel
  -- Ambient carried through gather (everything kss needs that gather does not write).
  let Amb : Assertion :=
    (.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      frameSlotsOwn kssFrame newSp **
      bytesRegion TshBuf typeBs ** bytesRegion tshPrefixOutPtr prefixBs **
      bytesRegion (inPtr + hdrLen) payloadBs **
      bytesRegion KssZk3 os **
      bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
      regOwns kssFreeTemps ** A ** F
  have hAmb : Amb.pcFree := by
    unfold Amb
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_frameSlotsOwn _ _
      | exact bytesRegion_pcFree _ _
      | exact hA
      | exact hF
      | exact (by pcf)
  have hgather := tshPostPrefixTypedToKssJal_spec v5 v29 v30 v31 typePrefix inPtr
    outPtr hdrLen payloadLen cellVal v10 v11 v12 old0 old1 old2 old3 old4 old5 hnz
  have hgatherF := cpsTripleWithin_frameR Amb hAmb hgather
  have hcount : segs.length < 2 ^ 64 := by
    simp only [segs, tshTypedSegs, List.length_cons, List.length_nil, Nat.reduceAdd]
    decide
  -- Gather scratch (x29–x31 + prefix cell) is not part of the kss ABI; frame it.
  let Fextra : Assertion :=
    (.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
      (.x31 ↦ᵣ (inPtr + hdrLen)) **
      (tshPrefixCellPtr ↦ₘ cellVal) ** F
  have hFextra : Fextra.pcFree := by
    unfold Fextra
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact hF
  have hkss := tshKssCallThenSuccess_spec vOld sp0 tshSegsBase outPtr segs os
    (1 : Word) v6 v7 inPtr v9 v18 typePrefix outPtr hdrLen payloadLen
    A Fextra hA hFextra hos hcount hsegsOk
  have c := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      -- Mid: gather post ** Amb → kss call pre
      simp only [Amb, segs, tshTypedSegs, tshKssCallPre, tshKssSregs, kssCallerPre,
        kssSegsIs_cons, kssSegsIs_nil, Fextra, sepConj_emp_right'] at hp ⊢
      -- `kssSegsIs` nests `base+16+8`; gather wrote flat `base+24` / `base+40`.
      -- Normalize deeper `+16` nests BEFORE `+16+8`, or `+16+8` misfires inside `+16+16+8`.
      -- Only the kss-pre goal has nested adds; gather post (`hp`) is already flat.
      rw [show (tshSegsBase + 16 : Word) + 16 = tshSegsBase + 32 from by bv_omega,
          show (tshSegsBase + 32 : Word) + 8 = tshSegsBase + 40 from by bv_omega,
          show (tshSegsBase + 16 : Word) + 8 = tshSegsBase + 24 from by bv_omega]
      have hlen3 : BitVec.ofNat 64 3 = (3 : Word) := rfl
      have h1 : BitVec.ofNat 64 typeBs.length = (1 : Word) := by
        simp [htypeLen]
      have hpref : BitVec.ofNat 64 prefixBs.length = cellVal := hcell.symm
      have hpay : BitVec.ofNat 64 payloadBs.length = payloadLen := hpayW.symm
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, hlen3, h1, hpref, hpay]
      xperm_hyp hp) hgatherF hkss
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [segs, Fextra] at hq ⊢
      exact hq) c

/-! ## `regOwn` entry adapter for typed gather→success

    Prefix `callWithin` returns `regOwn` on `t0`/`t1`/`t2`; gather leaf wants
    concrete `regIs`. Lift via `cpsTripleWithin_of_forall_regIs_to_regOwn`. -/

/-- Same as `tshTypedGatherThroughSuccess_spec` with `regOwn .x5/.x6/.x7` pre. -/
theorem tshTypedGatherThroughSuccess_regOwn_spec
    (v29 v30 v31 typePrefix inPtr outPtr hdrLen payloadLen cellVal : Word)
    (v10 v11 v12 old0 old1 old2 old3 old4 old5 : Word)
    (vOld sp0 v9 v18 : Word)
    (typeBs prefixBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hnz : typePrefix ≠ 0)
    (htypeLen : typeBs.length = 1)
    (hcell : cellVal = BitVec.ofNat 64 prefixBs.length)
    (hpayW : payloadLen = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ s ∈ tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen,
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let segs := tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let gatherFuel := 6 + 3 + 4 + 5 + 3 + 3
    let kssFuel := 1 + (19 + kssBodyFuelMulti segs) + 2
    let Rest : Assertion :=
      (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x1 ↦ᵣ vOld) ** (.x2 ↦ᵣ sp0) **
        frameSlotsOwn kssFrame newSp **
        (tshPrefixCellPtr ↦ₘ cellVal) **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
        bytesRegion TshBuf typeBs ** bytesRegion tshPrefixOutPtr prefixBs **
        bytesRegion (inPtr + hdrLen) payloadBs **
        bytesRegion KssZk3 os **
        bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
        regOwns kssFreeTemps ** A ** F
    let Post : Assertion :=
      (.x1 ↦ᵣ (tshKssJalPC + 4)) **
        (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
          inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
          ((.x29 ↦ᵣ cellVal) ** (.x30 ↦ᵣ tshSegsBase) **
            (.x31 ↦ᵣ (inPtr + hdrLen)) **
            (tshPrefixCellPtr ↦ₘ cellVal) ** F))
    cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
      ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) ** Rest) Post := by
  intro segs newSp gatherFuel kssFuel Rest Post
  have hinn : ∀ v5 v6 v7,
      cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
        ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** Rest) Post := by
    intro v5 v6 v7
    have h := tshTypedGatherThroughSuccess_spec v5 v29 v30 v31 typePrefix inPtr
      outPtr hdrLen payloadLen cellVal v10 v11 v12 old0 old1 old2 old3 old4 old5
      vOld sp0 v6 v7 v9 v18 typeBs prefixBs payloadBs os A F hA hF hnz htypeLen
      hcell hpayW hos hsegsOk
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [Rest] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [Post, segs] at hq ⊢
        exact hq) h
  have h7 : ∀ v5 v6,
      cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
        (((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** Rest) ** regOwn .x7) Post := by
    intro v5 v6
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v7 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hinn v5 v6 v7)
  have h6 : ∀ v5,
      cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
        (((.x5 ↦ᵣ v5) ** Rest ** regOwn .x7) ** regOwn .x6) Post := by
    intro v5
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v6 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h7 v5 v6)
  have h5 :
      cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
        ((Rest ** regOwn .x7 ** regOwn .x6) ** regOwn .x5) Post := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v5 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h6 v5)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h5

/-! ## Prefix return → typed gather through success (`H+220 → bodyExit`)

    Mid-reshape from `tshPostNthThenPrefixCall_spec` post (with gather ambient
    in `F`) into `tshTypedGatherThroughSuccess_regOwn_spec`. -/

/-- After short prefix call returns at `H+220`, run typed gather→kss→success.

    Requires `cellVal = 1` (prefix wrote the short-list byte count) and
    `prefixBs` already equal to the post-prefix out buffer. -/
theorem tshPrefixReturnThenTypedSuccess_spec
    (v29 v30 v31 typePrefix inPtr outPtr hdrLen payloadLen : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (sp0 v9 v18 offVal lenVal : Word)
    (typeBs prefixBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hnz : typePrefix ≠ 0)
    (htypeLen : typeBs.length = 1)
    (hcell : (1 : Word) = BitVec.ofNat 64 prefixBs.length)
    (hpayW : payloadLen = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ s ∈ tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen,
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let segs := tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let gatherFuel := 6 + 3 + 4 + 5 + 3 + 3
    let kssFuel := 1 + (19 + kssBodyFuelMulti segs) + 2
    let retPrefix := tshPrefixJalPC + 4
    cpsTripleWithin (gatherFuel + kssFuel) (H + 220) tshBodyExit fullCode
      ((.x1 ↦ᵣ retPrefix) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr prefixBs **
        (tshPrefixCellPtr ↦ₘ (1 : Word)) **
        (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x2 ↦ᵣ sp0) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        frameSlotsOwn kssFrame newSp **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
        bytesRegion TshBuf typeBs **
        bytesRegion (inPtr + hdrLen) payloadBs **
        bytesRegion KssZk3 os **
        bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
        regOwns kssFreeTemps ** A ** F)
      (((.x1 ↦ᵣ (tshKssJalPC + 4)) **
        (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
          inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
          ((.x29 ↦ᵣ (1 : Word)) ** (.x30 ↦ᵣ tshSegsBase) **
            (.x31 ↦ᵣ (inPtr + hdrLen)) **
            (tshPrefixCellPtr ↦ₘ (1 : Word)) **
            ((tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) ** F))))) := by
  intro segs newSp gatherFuel kssFuel retPrefix
  let Fnth : Assertion :=
    (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) ** F
  have hFnth : Fnth.pcFree := by
    unfold Fnth
    exact pcFree_sepConj pcFree_memIs (pcFree_sepConj pcFree_memIs hF)
  have hG := tshTypedGatherThroughSuccess_regOwn_spec v29 v30 v31 typePrefix inPtr
    outPtr hdrLen payloadLen (1 : Word) (0 : Word) tshPrefixOutPtr tshPrefixCellPtr
    old0 old1 old2 old3 old4 old5 retPrefix sp0 v9 v18 typeBs prefixBs payloadBs os
    A Fnth hA hFnth hnz htypeLen hcell hpayW hos hsegsOk
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Fnth, retPrefix] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [Fnth, segs] at hq ⊢
      xperm_hyp hq) hG

/-! ## Nth ok scratch → short prefix call (`H+160 → H+220`)

    Peeled `callReturnResult` success shape (`a0 = 0`, off/len cells, `regOwn`
    temps) into `tshPostNthThenPrefixCall_spec`. -/

/-- Success-status nth return (concrete, not `∃`) through prefix `callWithin`. -/
theorem tshNthOkThenPrefixCall_spec
    (v11 v12 v22 offVal lenVal hdrLen cellOld : Word)
    (outBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (h_len : ((offVal + lenVal) - hdrLen).toNat < 56)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_len : 0 < outBytes.length)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true) :
    let payloadLen := (offVal + lenVal) - hdrLen
    let retNth := tshNthJalPC + 4
    cpsTripleWithin ((1 + 8 + 6) + (1 + 8)) (H + 160) (tshPrefixJalPC + 4) fullCode
      ((.x1 ↦ᵣ retNth) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F)
      ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr
          (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + payloadLen.toNat))) **
        (tshPrefixCellPtr ↦ₘ (1 : Word)) ** F) := by
  intro payloadLen retNth
  have hinn : ∀ v5 v6 v7,
      cpsTripleWithin ((1 + 8 + 6) + (1 + 8)) (H + 160) (tshPrefixJalPC + 4) fullCode
        ((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr
            (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + payloadLen.toNat))) **
          (tshPrefixCellPtr ↦ₘ (1 : Word)) ** F) := by
    intro v5 v6 v7
    have h := tshPostNthThenPrefixCall_spec retNth v5 v6 v7 v11 v12 v22
      offVal lenVal hdrLen cellOld outBytes F hF h_len h_out_align h_out_len h_out_valid
    exact cpsTripleWithin_weaken (fun _ hp => by
        simp only [retNth] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [payloadLen] at hq ⊢
        exact hq) h
  have h7 : ∀ v5 v6,
      cpsTripleWithin ((1 + 8 + 6) + (1 + 8)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) ** F) **
          regOwn .x7)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr
            (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + payloadLen.toNat))) **
          (tshPrefixCellPtr ↦ₘ (1 : Word)) ** F) := by
    intro v5 v6
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v7 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hinn v5 v6 v7)
  have h6 : ∀ v5,
      cpsTripleWithin ((1 + 8 + 6) + (1 + 8)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x5 ↦ᵣ v5) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x7) **
          regOwn .x6)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr
            (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + payloadLen.toNat))) **
          (tshPrefixCellPtr ↦ₘ (1 : Word)) ** F) := by
    intro v5
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v6 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h7 v5 v6)
  have h5 :
      cpsTripleWithin ((1 + 8 + 6) + (1 + 8)) (H + 160) (tshPrefixJalPC + 4) fullCode
        (((.x1 ↦ᵣ retNth) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
          F ** regOwn .x7 ** regOwn .x6) **
          regOwn .x5)
        ((.x1 ↦ᵣ (tshPrefixJalPC + 4)) **
          (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          (.x11 ↦ᵣ tshPrefixOutPtr) ** (.x12 ↦ᵣ tshPrefixCellPtr) **
          (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ payloadLen) **
          (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
          bytesRegion tshPrefixOutPtr
            (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + payloadLen.toNat))) **
          (tshPrefixCellPtr ↦ₘ (1 : Word)) ** F) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun v5 => ?_)
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (h6 v5)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) h5

/-- Peel `callReturnResult` ∃ from a `cpsTripleWithin` precondition. -/
theorem tsh_cpsTripleWithin_callReturn_pre
    {N : Nat} {ret X : Word} {F Q : Assertion}
    (sp0 listBase indexW offsetPtr lenPtr oldOffset oldLen : Word)
    (csaved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (h : ∀ status offset len v11 v12,
        EvmAsm.Codegen.RlpListNthItemSAsm.Result bytes listBase listLen index
          oldOffset oldLen status offset len →
        cpsTripleWithin N (H + 160) ret fullCode
          (((.x1 ↦ᵣ X) **
            (((.x2 ↦ᵣ sp0) ** stackFree sp0 8 **
              EvmAsm.Codegen.RlpListNthItemSAsm.savedRegTail csaved) **
             ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
              (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
              regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
              (offsetPtr ↦ₘ offset) ** (lenPtr ↦ₘ len)))) ** F) Q) :
    cpsTripleWithin N (H + 160) ret fullCode
      (((.x1 ↦ᵣ X) **
        EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult sp0 listBase indexW
          offsetPtr lenPtr oldOffset oldLen csaved bytes listLen index) ** F) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, s1, s2, hd12, hu12, hP, hRs⟩ := hPR
  obtain ⟨t1, t2, hdt, hut, hXcRR, hFt⟩ := hP
  obtain ⟨u1, u2, hdu, huu, hX, hcRR⟩ := hXcRR
  unfold EvmAsm.Codegen.RlpListNthItemSAsm.callReturnResult at hcRR
  obtain ⟨status, offset, len, v11, v12, hBig⟩ := hcRR
  have hspl := (sepConj_pure_right u2).1 hBig
  exact h status offset len v11 v12 hspl.2 R hR s hcr
    ⟨hp, hcompat, s1, s2, hd12, hu12,
      ⟨t1, t2, hdt, hut, ⟨u1, u2, hdu, huu, hX, hspl.1⟩, hFt⟩, hRs⟩ hpc

/-! ## Nth ok → prefix → typed gather → success (`H+160 → bodyExit`) -/

/-- Peeled nth-success scratch through prefix call and typed multi-rate finish. -/
theorem tshNthOkThroughTypedSuccess_spec
    (v11 v12 v22 offVal lenVal hdrLen cellOld : Word)
    (v29 v30 v31 typePrefix inPtr outPtr : Word)
    (old0 old1 old2 old3 old4 old5 : Word)
    (sp0 v9 v18 : Word)
    (outBytes typeBs payloadBs os : List (BitVec 8))
    (A F : Assertion) (hA : A.pcFree) (hF : F.pcFree)
    (hnz : typePrefix ≠ 0)
    (htypeLen : typeBs.length = 1)
    (h_len : ((offVal + lenVal) - hdrLen).toNat < 56)
    (h_out_align : tshPrefixOutPtr.toNat % 8 = 0)
    (h_out_len : outBytes.length = 1)
    (h_out_valid : ∀ k, k < outBytes.length →
      isValidByteAccess (tshPrefixOutPtr + BitVec.ofNat 64 k) = true)
    (hpayW : ((offVal + lenVal) - hdrLen) = BitVec.ofNat 64 payloadBs.length)
    (hos : os.length = 200)
    (hsegsOk : ∀ s ∈ tshTypedSegs typeBs
        (outBytes.set 0 (BitVec.ofNat 8 (0xC0 + ((offVal + lenVal) - hdrLen).toNat)))
        payloadBs inPtr hdrLen,
      s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
        (∀ i, i < s.2.length →
          s.1.toNat + i < 2 ^ 64 ∧
          isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let payloadLen := (offVal + lenVal) - hdrLen
    let prefixBs := outBytes.set 0 (BitVec.ofNat 8 (0xC0 + payloadLen.toNat))
    let segs := tshTypedSegs typeBs prefixBs payloadBs inPtr hdrLen
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    let prefixFuel := (1 + 8 + 6) + (1 + 8)
    let gatherFuel := 6 + 3 + 4 + 5 + 3 + 3
    let kssFuel := 1 + (19 + kssBodyFuelMulti segs) + 2
    cpsTripleWithin (prefixFuel + (gatherFuel + kssFuel)) (H + 160) tshBodyExit fullCode
      ((.x1 ↦ᵣ (tshNthJalPC + 4)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        (.x21 ↦ᵣ hdrLen) ** (.x22 ↦ᵣ v22) **
        (tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) **
        bytesRegion tshPrefixOutPtr outBytes ** (tshPrefixCellPtr ↦ₘ cellOld) **
        (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
        (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
        (.x2 ↦ᵣ sp0) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
        frameSlotsOwn kssFrame newSp **
        (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
        ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
        ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
        bytesRegion TshBuf typeBs **
        bytesRegion (inPtr + hdrLen) payloadBs **
        bytesRegion KssZk3 os **
        bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
        regOwns kssFreeTemps ** A ** F)
      (((.x1 ↦ᵣ (tshKssJalPC + 4)) **
        (tshKssCallPost sp0 newSp (tshKssJalPC + 4) tshSegsBase outPtr segs
          inPtr v9 v18 typePrefix outPtr hdrLen payloadLen A **
          ((.x29 ↦ᵣ (1 : Word)) ** (.x30 ↦ᵣ tshSegsBase) **
            (.x31 ↦ᵣ (inPtr + hdrLen)) **
            (tshPrefixCellPtr ↦ₘ (1 : Word)) **
            ((tshNthOffPtr ↦ₘ offVal) ** (tshNthLenPtr ↦ₘ lenVal) ** F))))) := by
  intro payloadLen prefixBs segs newSp prefixFuel gatherFuel kssFuel
  have hcell : (1 : Word) = BitVec.ofNat 64 prefixBs.length := by
    simp only [prefixBs, List.length_set, h_out_len]
    rfl
  have hout_pos : 0 < outBytes.length := by omega
  let Amb : Assertion :=
    (.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) **
      (.x19 ↦ᵣ typePrefix) ** (.x20 ↦ᵣ outPtr) **
      (.x2 ↦ᵣ sp0) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
      frameSlotsOwn kssFrame newSp **
      (tshSegsBase ↦ₘ old0) ** ((tshSegsBase + 8) ↦ₘ old1) **
      ((tshSegsBase + 16) ↦ₘ old2) ** ((tshSegsBase + 24) ↦ₘ old3) **
      ((tshSegsBase + 32) ↦ₘ old4) ** ((tshSegsBase + 40) ↦ₘ old5) **
      bytesRegion TshBuf typeBs **
      bytesRegion (inPtr + hdrLen) payloadBs **
      bytesRegion KssZk3 os **
      bytesRegion outPtr (List.replicate 32 (0 : BitVec 8)) **
      regOwns kssFreeTemps ** A ** F
  have hAmb : Amb.pcFree := by
    unfold Amb
    repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_memIs
      | exact pcFree_frameSlotsOwn _ _
      | exact bytesRegion_pcFree _ _
      | exact hA
      | exact hF
      | exact (by pcf)
  have hpref := tshNthOkThenPrefixCall_spec v11 v12 v22 offVal lenVal hdrLen cellOld
    outBytes Amb hAmb h_len h_out_align hout_pos h_out_valid
  have hprefF := hpref  -- already framed with Amb as F
  have htail := tshPrefixReturnThenTypedSuccess_spec v29 v30 v31 typePrefix inPtr outPtr
    hdrLen payloadLen old0 old1 old2 old3 old4 old5 sp0 v9 v18 offVal lenVal
    typeBs prefixBs payloadBs os A F hA hF hnz htypeLen hcell hpayW hos
        (by simpa [prefixBs, payloadLen] using hsegsOk)
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [Amb, payloadLen, prefixBs] at hp ⊢
      xperm_hyp hp) hprefF htail
  exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => by
      simp only [payloadLen, prefixBs, segs] at hq ⊢
      exact hq) c


end EvmAsm.Codegen.TxSigningHashSpec
