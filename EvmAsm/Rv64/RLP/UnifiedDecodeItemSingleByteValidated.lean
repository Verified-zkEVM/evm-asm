/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemSingleByteValidated

  Phase B of issue #9373 — the VALIDATING singleByte RLP single-item decoder over UNTRUSTED input.
  A `singleByte` prefix (`p < 0x80`) is *always* a valid canonical RLP encoding of the one-byte
  string `[p]` (the prefix IS the data), so — unlike short/long byte strings and lists — there is
  no failure case: the decoder cannot reject. The "validating" interface is therefore a plain
  single-exit `cpsTripleWithin` whose post carries the success verdict
  `⌜decode (pfx :: rest) = some (.bytes [pfx], rest)⌝`, with NO validity hypotheses on the input.

  This is the `singleByte` arm of the eventual 5-way unified validating decoder (the untrusted
  analogue of `rlp_decode_single_item_reconverged_all_region`). It frames the full untrusted-decoder
  register/memory interface (`x12`/`x13 = regionBase`/`x14`/`x15 = L`/`bytesRegion`) through the
  register-only e1 handler so it composes uniformly with the other (branching) class arms.
-/

import EvmAsm.Rv64.RLP.Phase1ToPhase3SingleByte
import EvmAsm.Rv64.MemRegion
import EvmAsm.EL.RLP.ByteStringDecodeBridge

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.EL.RLP.ByteStringDecodeBridge
open EvmAsm.Rv64.Tactics

/-- **Validating singleByte single-item decoder, at offset 0.** From an untrusted
    `bytesRegion regionBase (pfx :: rest)` with a `singleByte` prefix (`pfx < 0x80`), the e1
    handler runs in 3 steps and the post carries `⌜decode (pfx :: rest) = some (.bytes [pfx], rest)⌝`.
    No validity hypotheses, no failure exit: a canonical single byte always decodes. -/
theorem rlp_decode_singleByte_validated
    (pfx : Byte) (rest : List Byte)
    (v10 v11Old v12 v14 v15 : Word)
    (regionBase : Word)
    (offset : BitVec 13) (base target : Word)
    (h_class : classifyPrefix pfx = .singleByte)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hd : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :
    cpsTripleWithin 3 base (target + 4)
      ((rlp_phase1_step_code 0x80 offset base).union
         (CodeReq.ofProg target rlp_phase3_single_byte_prog))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14) **
        (.x15 ↦ᵣ v15) ** bytesRegion regionBase (pfx :: rest))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0x80 : BitVec 12))) **
        (.x11 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14) **
        (.x15 ↦ᵣ v15) ** bytesRegion regionBase (pfx :: rest) **
        ⌜decode (pfx :: rest) = some (.bytes [pfx], rest)⌝) := by
  -- The success verdict is unconditional for a canonical single byte.
  have hsome : decode (pfx :: rest) = some (.bytes [pfx], rest) := by
    rw [decode_cons_eq_decodeAux_fuel,
        show 2 * rest.length + 2 = (2 * rest.length + 1) + 1 from rfl,
        decodeAux_cons_singleByte_eq_some_iff (2 * rest.length + 1) pfx rest h_class [pfx] rest]
    exact ⟨rfl, rfl⟩
  -- The register-only e1 handler, framed with the full untrusted-decoder state.
  have handler := rlp_phase1_e1_single_byte_of_class_spec_within pfx v10 v11Old offset base target
    htarget h_class hd
  have framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ regionBase) ** (.x14 ↦ᵣ v14) **
      (.x15 ↦ᵣ v15) ** bytesRegion regionBase (pfx :: rest))
    (by exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj pcFree_regIs (bytesRegion_pcFree _ _))))) handler
  -- Reshape the framed pre to the goal pre (xperm), and append the verdict to the post.
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) ?_ framed
  intro s hq
  have hgoal := (sepConj_pure_right s).2 ⟨hq, hsome⟩
  xperm_hyp hgoal

-- Concrete cross-check: a single byte `0x42` decodes to the one-byte string `[0x42]`.
example (regionBase base target : Word) (offset : BitVec 13) (v10 v11 v12 v14 v15 : Word)
    (htarget : (base + 4) + signExtend13 offset = target)
    (hd : (rlp_phase1_step_code 0x80 offset base).Disjoint
            (CodeReq.ofProg target rlp_phase3_single_byte_prog)) :=
  rlp_decode_singleByte_validated (0x42 : Byte) [0x99] v10 v11 v12 v14 v15 regionBase
    offset base target (by decide) htarget hd

end EvmAsm.Rv64.RLP
