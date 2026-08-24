/-
  EvmAsm.Codegen.Programs.Secp256k1PointDoubleBridge

  Discharge of the named residual `#12319` on the `secp256k1_point_double`
  registry row: the whole-routine triple `pointDouble_spec`
  (`Secp256k1PointDoubleSAsm.lean`) states its post against the RAW
  accelerator semantic `Accel.curveDbl Accel.secpP x y` plus a zeroed
  infinity branch, and nothing tied that to the SpecRef group law
  `EvmAsm.Stateless.SpecRef.Secp256k1.pointAdd`.  This module closes the
  gap: `pointDouble_spec_pointAdd` is the SAME triple — same step bound,
  same entry/exit, same `pdCr`, same precondition, same spatial
  footprint — with the post's arithmetic content restated so that
  `Accel.curveDbl` does NOT appear in it at all.

  * Infinity branch: `beBytesToNat yBE = 0` now additionally carries
    `pointAdd P P = none`, i.e. the machine's `a0 = 1` / 64-byte-zero
    output IS the reference identity `𝒪`.
  * Generic branch: the two output coordinates are pinned to `q.1`/`q.2`
    for a `q` with `pointAdd P P = some q`, and the staging arena holds
    `pairBytes 4 q`.  `Accel.curveDbl` is gone from the statement.

  where `P = some (beBytesToNat xBE, beBytesToNat yBE)`.

  The proof is a pure post-weakening (`cpsTripleWithin_weaken` with the
  identity on the precondition) over the two legs of
  `EvmAsm/Crypto/Secp256k1PointArith.lean`
  (`pointAdd_self_zero`, `pointAdd_self_of_ne_zero`); the `0 < y < p`
  side condition of the tangent leg is supplied by the branch's own pure
  fact `beBytesToNat yBE ≠ 0` together with the triple's existing
  representability guard `hylt : beBytesToNat yBE < Accel.secpP`.  No new
  hypothesis is introduced, so the derived triple's domain is EXACTLY
  that of `pointDouble_spec` and its non-vacuity is inherited; the
  bridge's own hypothesis bundle is witnessed (and shown load-bearing by
  two negative controls) in `Secp256k1PointArith`.

  NOT claimed here: any whole-routine triple for `secp256k1_point_add`
  (`secp256k1PointAdd_prog`), and no group law — see the SCOPE note in
  `Secp256k1PointArith`.  The chord leg `pointAdd_of_fst_ne` is proved
  there and is what that lane will consume.
-/

import EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsm
import EvmAsm.Crypto.Secp256k1PointArith

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1PointDoubleSAsm

open Secp256k1FieldConvSAsm (secfBeToLeFn)
open Secp256k1FieldConvSAsm (secfLeToBeFn)
open Secp256k1FieldIsZeroSAsm (secfIsZero32Fn)
open Secp256k1FieldLeavesSAsm (secfZero32Fn)
open EvmAsm.Stateless.SpecRef.Secp256k1 (pointAdd)

/-- **`secp256k1_point_double` against the SpecRef group law** — the
    `#12319` bridge.  Identical to `pointDouble_spec` in step bound,
    entry/exit, `CodeReq`, precondition and spatial footprint; the post's
    arithmetic is restated so `Accel.curveDbl` never appears:

    * `beBytesToNat yBE = 0` ⇒ `pointAdd P P = none` and the output is
      the 64-byte zero point with `a0 = 1` (arena untouched);
    * otherwise there is a `q` with `pointAdd P P = some q`, the output
      BE-encodes `q`, `a0 = 0`, and the arena holds `pairBytes 4 q`,

    where `P = some (beBytesToNat xBE, beBytesToNat yBE)`. -/
theorem pointDouble_spec_pointAdd (sp0 inPtr outPtr ret v8 v9 : Word)
    (xBE yBE oX oY ws : List (BitVec 8))
    (hxlen : xBE.length = 32) (hylen : yBE.length = 32)
    (hoXlen : oX.length = 32) (hoYlen : oY.length = 32)
    (hwslen : ws.length = 64)
    (hwfX : Region.wf ⟨inPtr, xBE⟩) (hwfY : Region.wf ⟨inPtr + 32, yBE⟩)
    (hoal : outPtr.toNat % 8 = 0) (hoov : outPtr.toNat + 64 < 2 ^ 64)
    (hovalid : ∀ k, k < 64 → isValidMemAddr (outPtr + BitVec.ofNat 64 k) = true)
    (harval : ∀ j, j < 64 → isValidMemAddr (arenaB + BitVec.ofNat 64 j) = true)
    -- the arena window, SYMBOLISED (`GuestAddrs.secc_le_p1/_p2`) rather
    -- than spelled as bare layout literals the way `pointDouble_spec`
    -- still does — the #12648 symbolisation this seam was waiting for
    (hdIn : inPtr.toNat + 64 ≤ GuestAddrs.secc_le_p1
      ∨ GuestAddrs.secc_le_p2 ≤ inPtr.toNat)
    (hdOut : outPtr.toNat + 64 ≤ GuestAddrs.secc_le_p1
      ∨ GuestAddrs.secc_le_p2 ≤ outPtr.toNat)
    (hxlt : beBytesToNat xBE < Accel.secpP)
    (hylt : beBytesToNat yBE < Accel.secpP)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + pdFrame.length
        + (27 + ((secfIsZero32Fn 0 []).body.steps + 1)
            + ((secfBeToLeFn 0 0 [] []).body.steps + 1) * 2
            + ((secfLeToBeFn 0 0 [] []).body.steps + 1) * 2
            + ((secfZero32Fn 0 []).body.steps + 1) * 2)
        + pdFrame.length + 1 + 1)
      (GuestAddrs.secp256k1_point_double : Word) ret pdCr
      ((.x2 ↦ᵣ sp0) ** regsAt pdFrame (pdVals ret v8 v9)
        ** frameSlotsOwn pdFrame (sp0 + signExtend12 (-32 : BitVec 12))
        ** (((.x0 : Reg) ↦ᵣ (0 : Word))
          ** ((.x10 : Reg) ↦ᵣ inPtr) ** ((.x11 : Reg) ↦ᵣ outPtr)
          ** regOwns convScratch
          ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
          ** bytesRegion outPtr oX ** bytesRegion (outPtr + 32) oY
          ** bytesRegion arenaB ws))
      ((.x2 ↦ᵣ sp0) ** regsAt pdFrame (pdVals ret v8 v9)
        ** frameSlotsSaved pdFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (pdVals ret v8 v9)
        ** (fun hp =>
            ((⌜beBytesToNat yBE = 0
              ∧ pointAdd (some (beBytesToNat xBE, beBytesToNat yBE))
                  (some (beBytesToNat xBE, beBytesToNat yBE)) = none⌝
              ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (1 : Word))
              ** regOwns a0Rest
              ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
              ** bytesRegion outPtr (List.replicate 32 (0 : BitVec 8))
              ** bytesRegion (outPtr + 32) (List.replicate 32 (0 : BitVec 8))
              ** bytesRegion arenaB ws) hp)
            ∨ (∃ q oX' oY',
              ((⌜beBytesToNat yBE ≠ 0
                ∧ pointAdd (some (beBytesToNat xBE, beBytesToNat yBE))
                    (some (beBytesToNat xBE, beBytesToNat yBE)) = some q
                ∧ beBytesToNat oX' = q.1
                ∧ oX'.length = 32
                ∧ beBytesToNat oY' = q.2
                ∧ oY'.length = 32⌝
                ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x10 : Reg) ↦ᵣ (0 : Word))
                ** regOwns a0Rest
                ** bytesRegion inPtr xBE ** bytesRegion (inPtr + 32) yBE
                ** bytesRegion outPtr oX' ** bytesRegion (outPtr + 32) oY'
                ** bytesRegion arenaB (pairBytes 4 q)) hp)))) := by
  refine cpsTripleWithin_weaken (fun _ h => h) ?_
    (pointDouble_spec sp0 inPtr outPtr ret v8 v9 xBE yBE oX oY ws
      hxlen hylen hoXlen hoYlen hwslen hwfX hwfY hoal hoov hovalid harval
      hdIn hdOut hxlt hylt halign)
  intro h hq
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)) h hq
  intro h' hd
  rcases hd with hL | ⟨oX', oY', hR⟩
  · -- infinity branch: `y = 0`, so the group law returns `𝒪`
    refine Or.inl ?_
    rw [sepConj_pure_left] at hL ⊢
    refine ⟨⟨hL.1, ?_⟩, hL.2⟩
    rw [hL.1]
    exact Secp256k1PointArith.pointAdd_self_zero _
  · -- generic branch: `0 < y < p`, so the group law IS tangent doubling
    refine Or.inr ⟨Accel.curveDbl Accel.secpP (beBytesToNat xBE) (beBytesToNat yBE),
      oX', oY', ?_⟩
    rw [sepConj_pure_left] at hR ⊢
    obtain ⟨⟨hy0, hxeq, hxl, hyeq, hyl⟩, hrest⟩ := hR
    exact ⟨⟨hy0, Secp256k1PointArith.pointAdd_self_of_ne_zero hy0 hylt,
      hxeq, hxl, hyeq, hyl⟩, hrest⟩

end Secp256k1PointDoubleSAsm

end EvmAsm.Codegen
