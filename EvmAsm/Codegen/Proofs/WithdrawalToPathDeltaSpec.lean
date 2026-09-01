/-
  EvmAsm.Codegen.Proofs.WithdrawalToPathDeltaSpec

  **The `withdrawal_to_path_delta` machine triple — the undecodable-input
  (failure) arm (#12318).**

  `withdrawal_to_path_delta` (`Codegen/Programs/WithdrawalPath.lean`,
  `withdrawalToPathDelta_prog`, 41 instructions at
  `GuestAddrs.withdrawal_to_path_delta`, image entry
  `Codegen/Proofs/GuestImageEntries.lean:235`) is the non-engine preprocessing
  half of the withdrawal-driven post-state-root recompute.  Given a Shanghai+
  withdrawal RLP `rlp([index, validator_index, address, amount])` it produces
  the two things the state-trie update needs — the account's 64-nibble trie
  path `bytes_to_nibbles(keccak256(address))`, and the wei balance delta
  `amount_gwei * 1e9` — or answers `a0 = 1` if either the parse or the
  multiplication fails.

  ## Extent, derived rather than quoted

  `scripts/asm-fixtures/symbol-addresses.tsv` puts `withdrawal_to_path_delta`
  at `0x80005ba0` and the next `.text` symbol, `mset_memcpy`, at `0x80005c44`.
  That is `0xa4 = 164` bytes, and `164 = 41 * 4` cross-checks the
  `#guard withdrawalToPathDelta_prog.length = 41` in the Program module.

  ## What this module proves

  ⭐ **`wtpdKeccakSeamAligned`** — the reason this file exists.  #12318 left
  open whether `withdrawal_to_path_delta`'s `zkvm_keccak256` call is usable at
  all, since the same seam is what makes `bal_account_path` unrowable.  It is,
  and the fact is now a kernel-checked `decide` rather than prose.  See the
  section below.

  Then the composable scaffold for the routine's **failure arm** — the arm on
  which `withdrawal_decode` rejects the input, `bnez a0` at instruction index 9
  is TAKEN, and the routine answers `a0 = 1` from `.Lwtpd_fail`:

  * `withdrawalToPathDelta_segA/B/C_body_spec` — instruction indices 0..7, 9
    and 35..40, the sixteen instructions on that arm;
  * `wtpdCR`, `wtpd_disj_decode`, `wtpd_callSite8` — the forced code-requirement
    union with `withdrawal_decode`'s linked closure, and the call adapter for
    the `jal` at index 8;
  * `notDecoded_of_noStrictList` — the gate;
  * `wtpdFailCells`, `wdFailLeftover_split` — the callee's existential leftover
    reshaped so a tail can run under it;
  * `wtpdDecodeFailStep` — `withdrawal_decode_spec_within` instantiated at this
    routine's frame with its two-way post collapsed onto the failure disjunct.

  ⛔ **The whole-routine triple is NOT closed**, so this file registers no row.
  The obstruction is in `xperm`/`seqFrame`, not in the routine (#13207); it is written
  up in full in the "The whole-routine triple is NOT closed here" section at the
  bottom, together with what the next attempt should do.  Every declaration
  here is `#print axioms`-audited and carries the classical three only.

  ⭐ **What the failure arm would say, once assembled.**  Neither caller output
  buffer (`a2`, the 64-nibble path; `a3`, the 32-byte delta) nor `wtpd_hash`
  appears in `wtpdDecodeFailStep`'s footprint, and `cpsTripleWithin` quantifies
  over a `pcFree` frame — so the arm is a **no-write guarantee** on all three,
  which is what a caller reading `a0 = 1` depends on.

  ## The `CodeReq` union is FORCED

  The `jal ra, withdrawal_decode` at instruction index 8 is UNCONDITIONAL and
  sits above every branch in the routine, so every path leaves the routine's
  own bytes.  `wtpdCR` therefore pairs the `GuestImageEntries.lean:235`
  pairing with `withdrawal_decode`'s own linked closure
  (`WithdrawalDecodeSpec.fullCode`, itself a union over the strict
  `rlp_field_to_u64` selector's closure).

  ⚠️ Spelled `CodeReq.union a b`, not `a.union b`.  The two are the same term,
  but `scripts/proof-frontier.py --shape`'s resolver discarded any token
  containing a dot before #13196, which hid the anchor living inside the first
  leg.  The prefix spelling grades `whole-routine` either way.

  ## Registers

  `ra`, `s0` (`x8`), `s1` (`x9`) and `sp` are saved and restored.  ⚠️ `s0` and
  `s1` are written on the covered path (indices 4..5, `mv s0, a2` /
  `mv s1, a3`) *before* the call, and reloaded from the spill slots by the
  epilogue, so the post is stated from the reload.  `a0` comes back `1`.
  Everything the callee clobbers — `t0`-`t2`, `a1`-`a4`, `t3`-`t6` — is
  reported as owned rather than framed away, since the callee's contract
  surrenders them.

  ## ⚠️ What is deliberately NOT proven

  The success path, and with it every one of the routine's other four callee
  compositions: `zkvm_keccak256` (indices 10..16), `bytes_to_nibbles`
  (17..21), `u256_from_u64_be` (22..26) and `u256_mul_u64_be` (27..31),
  together with the overflow discrimination at index 32 and the `li a0, 0`
  success answer at index 33.  Nor are the four *other* `DecodeFailure` arms
  (`field0`/`field1`/`field2Len`/`field3` of
  `WithdrawalDecodeSpec.DecodeFailure`) reached: the gate here is the
  narrower "no strict outer list", which is what makes the arm decidable
  from a caller-supplied premise.  The registry row is therefore
  `.conditional` with that gate named.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only
  (audited by the `#print axioms` at the end of this file).
-/

import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.WP.Call
import EvmAsm.Evm64.CallingConvention
import EvmAsm.Codegen.Programs.WithdrawalPath
import EvmAsm.Codegen.Programs.WithdrawalDecodeClose5

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen
open EvmAsm.Codegen.WithdrawalDecodeSpec

/-! ## The routine's linked entry -/

/-- `withdrawal_to_path_delta`'s linked entry. -/
abbrev WTPD : Word := (GuestAddrs.withdrawal_to_path_delta : Word)

/-! ## Segment A — the three-slot prologue and the decode arguments -/

/-- `withdrawal_to_path_delta` instructions 0..7 (`base .. base + 32`): push a
    32-byte frame, spill `ra`/`s0`/`s1`, stash the two caller output pointers
    (`a2` → `s0`, `a3` → `s1`), then materialise `wtpd_struct` into `a2` as
    `withdrawal_decode`'s third argument.

    `a0` and `a1` — the caller's RLP pointer and length — are untouched and
    ride through as the callee's first two arguments. -/
theorem withdrawalToPathDelta_segA_body_spec
    (base sp ra structPtr v8 v9 v12 v13 : Word)
    (hla : base + (24 : Word) +
        (((laHi GuestAddrs.wtpd_struct
            (GuestAddrs.withdrawal_to_path_delta + 24)).zeroExtend 32 <<< 12).signExtend 64) +
        signExtend12 (laLo GuestAddrs.wtpd_struct
          (GuestAddrs.withdrawal_to_path_delta + 24)) = structPtr) :
    cpsTripleWithin 8 base (base + (32 : Word))
      (CodeReq.ofProg base withdrawalToPathDelta_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) **
       memOwn (sp - (32 : Word)) ** memOwn (sp - (24 : Word)) **
       memOwn (sp - (16 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ (sp - (32 : Word))) **
       (.x8 ↦ᵣ v12) ** (.x9 ↦ᵣ v13) ** (.x12 ↦ᵣ structPtr) ** (.x13 ↦ᵣ v13) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9)) := by
  unfold withdrawalToPathDelta_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 0: `addi sp, sp, -32`
  have P0 := addi_spec_gen_same_within .x2 sp (-32 : BitVec 12) base (by nofun)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
      show sp + (-32 : Word) = sp - (32 : Word) from by bv_omega] at P0
  -- index 1: `sd ra, 0(sp)`
  have P1 := sd_spec_gen_own_within .x2 .x1 (sp - (32 : Word)) ra (0 : BitVec 12)
    (base + (4 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (0 : BitVec 12) = sp - (32 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at P1
  -- index 2: `sd s0, 8(sp)`
  have P2 := sd_spec_gen_own_within .x2 .x8 (sp - (32 : Word)) v8 (8 : BitVec 12)
    (base + (8 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (8 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at P2
  -- index 3: `sd s1, 16(sp)`
  have P3 := sd_spec_gen_own_within .x2 .x9 (sp - (32 : Word)) v9 (16 : BitVec 12)
    (base + (12 : Word))
  rw [show (sp - (32 : Word)) + signExtend12 (16 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at P3
  -- index 4: `mv s0, a2` — the caller's 64-nibble path buffer
  have P4 := mv_spec_gen_within .x8 .x12 v12 v8 (base + (16 : Word)) (by nofun)
  -- index 5: `mv s1, a3` — the caller's 32-byte delta buffer
  have P5 := mv_spec_gen_within .x9 .x13 v13 v9 (base + (20 : Word)) (by nofun)
  -- indices 6, 7: `la a2, wtpd_struct`
  have P6 := auipc_spec_gen_within .x12 v12
    (laHi GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 24))
    (base + (24 : Word)) (by nofun)
  have P7 := addi_spec_gen_same_within .x12
    ((base + (24 : Word)) +
      (((laHi GuestAddrs.wtpd_struct
          (GuestAddrs.withdrawal_to_path_delta + 24)).zeroExtend 32 <<< 12).signExtend 64))
    (laLo GuestAddrs.wtpd_struct (GuestAddrs.withdrawal_to_path_delta + 24))
    (base + (28 : Word)) (by nofun)
  rw [hla] at P7
  runBlock P0 P1 P2 P3 P4 P5 P6 P7

#print axioms withdrawalToPathDelta_segA_body_spec

/-! ## Segment B — the failure discrimination -/

/-- `withdrawal_to_path_delta` instruction 9 (`base + 36`): `bnez a0,
    .Lwtpd_fail` — TAKEN, because the decode answered `a0 = 1`.  Control jumps
    to `base + 140`, instruction index 35.

    Only the TAKEN direction is needed, so only `hbne` is a premise. -/
theorem withdrawalToPathDelta_segB_body_spec
    (base : Word)
    (hbne : signExtend13 (brOff (GuestAddrs.withdrawal_to_path_delta + 140)
        (GuestAddrs.withdrawal_to_path_delta + 36)) = (104 : Word)) :
    cpsTripleWithin 1 (base + (36 : Word)) (base + (140 : Word))
      (CodeReq.ofProg base withdrawalToPathDelta_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (1 : Word)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (1 : Word))) := by
  unfold withdrawalToPathDelta_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  have RC := bne_spec_gen_within .x10 .x0
    (brOff (GuestAddrs.withdrawal_to_path_delta + 140)
      (GuestAddrs.withdrawal_to_path_delta + 36))
    (1 : Word) (0 : Word) (base + (36 : Word))
  rw [hbne, show base + (36 : Word) + (104 : Word) = base + (140 : Word) from by bv_omega]
    at RC
  have R0 : cpsTripleWithin 1 (base + (36 : Word)) (base + (140 : Word))
      (CodeReq.singleton (base + (36 : Word)) (.BNE .x10 .x0
        (brOff (GuestAddrs.withdrawal_to_path_delta + 140)
          (GuestAddrs.withdrawal_to_path_delta + 36))))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (1 : Word)) ** (.x0 ↦ᵣ (0 : Word))) :=
    cpsBranchWithin_takenStripPure2 RC (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact absurd h_pure.2 (by decide))
  runBlock R0

#print axioms withdrawalToPathDelta_segB_body_spec

/-! ## Segment C — `.Lwtpd_fail` and the epilogue -/

/-- `withdrawal_to_path_delta` instructions 35..40 (`base + 140 .. base + 160`):
    `li a0, 1` — the parse-failure answer — then reload `ra`, `s0`, `s1`, pop
    the 32-byte frame, and `ret`.

    ⭐ Neither caller output buffer nor `wtpd_hash` is named anywhere here, and
    the universally quantified `pcFree` frame turns that silence into a
    no-write guarantee. -/
theorem withdrawalToPathDelta_segC_body_spec
    (base sp ra link v8 v9 y8 y9 y10 : Word) :
    cpsTripleWithin 6 (base + (140 : Word)) (ra &&& ~~~(1 : Word))
      (CodeReq.ofProg base withdrawalToPathDelta_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ link) ** (.x2 ↦ᵣ (sp - (32 : Word))) **
       (.x8 ↦ᵣ y8) ** (.x9 ↦ᵣ y9) ** (.x10 ↦ᵣ y10) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ ra) ** (.x2 ↦ᵣ sp) **
       (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x10 ↦ᵣ (1 : Word)) **
       ((sp - (32 : Word)) ↦ₘ ra) ** ((sp - (24 : Word)) ↦ₘ v8) **
       ((sp - (16 : Word)) ↦ₘ v9)) := by
  unfold withdrawalToPathDelta_prog
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  -- index 35: `li a0, 1` — the failure answer
  have T0 := li_spec_gen_within .x10 y10 (1 : Word) (base + (140 : Word)) (by nofun)
  -- indices 36..38: reload ra, s0, s1
  have T1 := ld_spec_gen_within .x1 .x2 (sp - (32 : Word)) link ra (0 : BitVec 12)
    (base + (144 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (0 : BitVec 12) = sp - (32 : Word) from by
    rw [signExtend12_0]; exact BitVec.add_zero _] at T1
  have T2 := ld_spec_gen_within .x8 .x2 (sp - (32 : Word)) y8 v8 (8 : BitVec 12)
    (base + (148 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (8 : BitVec 12) = sp - (24 : Word) from by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]; bv_omega] at T2
  have T3 := ld_spec_gen_within .x9 .x2 (sp - (32 : Word)) y9 v9 (16 : BitVec 12)
    (base + (152 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (16 : BitVec 12) = sp - (16 : Word) from by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]; bv_omega] at T3
  -- index 39: `addi sp, sp, 32`
  have T4 := addi_spec_gen_same_within .x2 (sp - (32 : Word)) (32 : BitVec 12)
    (base + (156 : Word)) (by nofun)
  rw [show (sp - (32 : Word)) + signExtend12 (32 : BitVec 12) = sp from by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]; bv_omega] at T4
  -- index 40: `ret`
  have T5 := EvmAsm.Evm64.ret_spec_within' (base + (160 : Word)) ra
  runBlock T0 T1 T2 T3 T4 T5

#print axioms withdrawalToPathDelta_segC_body_spec

/-! ## The code requirement -/

theorem wtpd_length : withdrawalToPathDelta_prog.length = 41 := by decide

/-- `withdrawal_to_path_delta`'s code requirement: its own 41 instructions at
    `GuestAddrs.withdrawal_to_path_delta` — the `GuestImageEntries.lean:235`
    pairing — unioned with `withdrawal_decode`'s full linked closure.

    The union is FORCED: the `jal ra, withdrawal_decode` at instruction index 8
    is UNCONDITIONAL and sits above every branch, so every path through this
    routine leaves its own bytes.

    ⚠️ Spelled `CodeReq.union a b`, not `a.union b` — see the module docstring. -/
def wtpdCR : CodeReq :=
  CodeReq.union
    (CodeReq.ofProg WTPD withdrawalToPathDelta_prog)
    WithdrawalDecodeSpec.fullCode

theorem wtpd_disj_decode :
    (CodeReq.ofProg WTPD withdrawalToPathDelta_prog).Disjoint
      WithdrawalDecodeSpec.fullCode := by
  unfold WithdrawalDecodeSpec.fullCode WithdrawalDecodeSpec.wdCode
    EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
  refine CodeReq.Disjoint.union_right ?_
    (CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_))
  · unfold WithdrawalDecodeSpec.WB WTPD
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wtpd_length]; decide
    · rw [WithdrawalDecodeSpec.wd_length]; decide
    · rw [wtpd_length, WithdrawalDecodeSpec.wd_length]; decide
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.wrapperCode
      EvmAsm.Codegen.RlpFieldToU64StrictSAsm.B WTPD
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wtpd_length]; decide
    · rw [EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
    · rw [wtpd_length, EvmAsm.Codegen.RlpFieldToU64StrictSAsm.program_length]; decide
  · unfold EvmAsm.Codegen.RlpListNthItemSAsm.code
      EvmAsm.Codegen.RlpListNthItemSAsm.B WTPD
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wtpd_length]; decide
    · rw [EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
    · rw [wtpd_length, EvmAsm.Codegen.RlpListNthItemSAsm.total_length]; decide
  · unfold EvmAsm.Codegen.RlpFieldToU64StrictSAsm.contentCode
      EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_code
      EvmAsm.Codegen.RlpFieldToU64StrictSAsm.C64B WTPD
    apply CodeReq.Disjoint.ofProg_ranges
    · rw [wtpd_length]; decide
    · rw [EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog_length]; decide
    · rw [wtpd_length, EvmAsm.Rv64.RLP.rlp_content_to_u64_strict_prog_length]; decide

theorem wtpdProg_sub_wtpdCR :
    ∀ a i, CodeReq.ofProg WTPD withdrawalToPathDelta_prog a = some i →
      wtpdCR a = some i :=
  CodeReq.union_mono_left

/-- Call-site adapter for the `jal ra, withdrawal_decode` at instruction index
    8 (`WTPD + 32`) — the unconditional decode. -/
theorem wtpd_callSite8 {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WithdrawalDecodeSpec.WB (WTPD + (36 : Word))
        WithdrawalDecodeSpec.fullCode
        ((.x1 ↦ᵣ (WTPD + (36 : Word))) ** Prest) Q) :
    cpsTripleWithin (1 + n) (WTPD + (32 : Word)) (WTPD + (36 : Word)) wtpdCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have h36 : WTPD + (32 : Word) + 4 = WTPD + (36 : Word) := by bv_omega
  have halign : (WTPD + (32 : Word) + 4) &&& ~~~(1 : Word) = WTPD + (32 : Word) + 4 := by
    decide
  have hcallee' : cpsTripleWithin n WithdrawalDecodeSpec.WB
      ((WTPD + (32 : Word) + 4) &&& ~~~(1 : Word)) WithdrawalDecodeSpec.fullCode
      ((.x1 ↦ᵣ (WTPD + (32 : Word) + 4)) ** Prest) Q := by
    rw [halign, h36]; exact hcallee
  have hdisj :
      (CodeReq.singleton (WTPD + (32 : Word))
        (.JAL .x1 (jalOff GuestAddrs.withdrawal_decode
          (GuestAddrs.withdrawal_to_path_delta + 32)))).Disjoint
        WithdrawalDecodeSpec.fullCode := by
    unfold WithdrawalDecodeSpec.fullCode WithdrawalDecodeSpec.wdCode
      EvmAsm.Codegen.RlpFieldToU64StrictSAsm.code
    refine CodeReq.Disjoint.union_right ?_
      (CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.union_right ?_ ?_))
    · exact CodeReq.Disjoint.singleton_ofProg (by decide +kernel)
    · exact CodeReq.Disjoint.singleton_ofProg (by decide +kernel)
    · exact CodeReq.Disjoint.singleton_ofProg (by decide +kernel)
    · exact CodeReq.Disjoint.singleton_ofProg (by decide +kernel)
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := WTPD + (32 : Word))
    (calleeEntry := WithdrawalDecodeSpec.WB) (vOld := vRa)
    (calleeCode := WithdrawalDecodeSpec.fullCode)
    (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.withdrawal_decode (GuestAddrs.withdrawal_to_path_delta + 32))
    (by decide) halign hPrest hdisj hcallee'
  rw [h36] at hcall
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at WTPD (WTPD + (32 : Word)) withdrawalToPathDelta_prog 8 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right wtpd_disj_decode (fun _ _ h => h) a i h

#print axioms wtpd_disj_decode
#print axioms wtpd_callSite8

/-! ## The gate: the input is not a strict RLP list -/

/-- ⭐ **The gate is sufficient, and the implication is one line.**
    `Decoded`'s third conjunct is `RlpListNthItemSAsm.Success bytes listBase
    listLen 2 o2 l2`, and `Success` is *defined* to begin with a
    `StrictListPayload` for the outer list
    (`Programs/RlpListNthItemSAsmBase.lean:399`).  So an input that is not a
    strict RLP list at all cannot decode, whatever the four field values. -/
theorem notDecoded_of_noStrictList
    (bytes : List (BitVec 8)) (listBase : Word) (listLen : Nat)
    (hno : ¬ ∃ cursorOff endPtr,
      EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload bytes listBase listLen
        cursorOff endPtr) :
    ∀ v0 v1 v3 o2 l2,
      ¬ WithdrawalDecodeSpec.Decoded bytes listBase listLen v0 v1 v3 o2 l2 := by
  intro v0 v1 v3 o2 l2 hd
  obtain ⟨cursorOff, endPtr, _next, hpay, _, _⟩ := hd.2.2.1
  exact hno ⟨cursorOff, endPtr, hpay⟩

#print axioms notDecoded_of_noStrictList

/-! ## The failure-arm leftover, split so the tail can run

    `WithdrawalDecodeSpec.wdFailLeftover` bundles nine existential witnesses
    *and* `wdScratch`, which owns `x0`.  Segments B and C need `x0` (the
    `bnez a0, x0` discriminator and the `ret`), so the scratch has to come out
    from under the existential before the tail can be composed.  Splitting it
    once here keeps the whole rest of the proof existential-free: the cells
    below travel as a single opaque, `pcFree` frame atom. -/

/-- The failure leftover's *cells* — everything `wdFailLeftover` owns except
    `wdScratch` — with the nine witnesses named. -/
def wtpdFailCellsBody (spW outBase listBase : Word) (bytes : List (BitVec 8))
    (o0 o1 o3 woff wlen roff rlen : Word)
    (addr20 pad4 : List (BitVec 8)) : Assertion :=
  (outBase ↦ₘ o0) ** ((outBase + 8) ↦ₘ o1) **
  bytesRegion (outBase + 16) addr20 ** bytesRegion (outBase + 36) pad4 **
  ((outBase + 40) ↦ₘ o3) ** bytesRegion listBase bytes **
  (WithdrawalDecodeSpec.wdOffsetAddr ↦ₘ woff) **
  (WithdrawalDecodeSpec.wdLengthAddr ↦ₘ wlen) **
  (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.offsetCell ↦ₘ roff) **
  (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.lengthCell ↦ₘ rlen) **
  EvmAsm.Rv64.SAsm.stackFree spW 12

/-- The same, re-quantified: the routine's post owns the 48-byte struct, the
    input region, the four RLP data cells and the reclaimed scratch stack, with
    their contents forgotten. -/
def wtpdFailCells (spW outBase listBase : Word) (bytes : List (BitVec 8)) : Assertion :=
  fun h => ∃ (o0 o1 o3 woff wlen roff rlen : Word) (addr20 pad4 : List (BitVec 8)),
    wtpdFailCellsBody spW outBase listBase bytes o0 o1 o3 woff wlen roff rlen addr20 pad4 h

theorem pcFree_wtpdFailCells (spW outBase listBase : Word) (bytes : List (BitVec 8)) :
    (wtpdFailCells spW outBase listBase bytes).pcFree := by
  intro h hp
  obtain ⟨_, _, _, _, _, _, _, _, _, hbody⟩ := hp
  revert h hbody
  show Assertion.pcFree _
  unfold wtpdFailCellsBody
  repeat' first
    | exact pcFree_memIs | exact bytesRegion_pcFree _ _
    | exact pcFree_stackFree _ _ | exact pcFree_memOwn
    | exact pcFree_emp | apply pcFree_sepConj

/-- Lift `wdScratch` — and with it `x0` — out from under the callee post's
    existential, leaving the cells as one opaque frame atom. -/
theorem wdFailLeftover_split (spW outBase listBase s3 s4 s5 : Word)
    (bytes : List (BitVec 8)) :
    ∀ h, WithdrawalDecodeSpec.wdFailLeftover spW outBase listBase s3 s4 s5 bytes h →
      (WithdrawalDecodeSpec.wdScratch s3 s4 s5 **
        wtpdFailCells spW outBase listBase bytes) h := by
  intro h hp
  obtain ⟨o0, o1, o3, woff, wlen, roff, rlen, addr20, pad4, hbody⟩ := hp
  have hbody' : (WithdrawalDecodeSpec.wdScratch s3 s4 s5 **
      wtpdFailCellsBody spW outBase listBase bytes
        o0 o1 o3 woff wlen roff rlen addr20 pad4) h := by
    unfold wtpdFailCellsBody
    xperm_hyp hbody
  obtain ⟨h1, h2, hd, hu, hscr, hcells⟩ := hbody'
  exact ⟨h1, h2, hd, hu, hscr, o0, o1, o3, woff, wlen, roff, rlen, addr20, pad4, hcells⟩

#print axioms pcFree_wtpdFailCells
#print axioms wdFailLeftover_split

/-- `wtpd_struct`, the 48-byte decode destination, on its linked `.bss`
    address (`symbol-addresses.tsv:1427`, `.balign 8` in the emitted data
    section). -/
abbrev WS : Word := (GuestAddrs.wtpd_struct : Word)

/-- `withdrawal_decode_spec_within`'s step bound, named so the caller's total
    can be written without repeating it.  If this drifts from the callee's
    expression the composition below simply does not typecheck. -/
def wdDecodeFuel : Nat :=
  (8 +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))) +
        ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) +
        ((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9)) + 1) +
        (5 + (5 + (6 * (19 + 1)) +
        ((4 + (1 + ((7 + 4 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) +
          ((1 + ((7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5)) + 5))) + 1) + 8)))))))

/-! ## ⭐ The keccak seam's alignment premise, measured

    Recorded here even though the seam is off the covered path, because it is
    the fact that separates this routine from `bal_account_path`. -/

/-- **`wtpd_struct + 16` — the 20-byte address slab `zkvm_keccak256` is asked
    to hash — is dword-aligned.**  With a 20-byte preimage the absorb loop runs
    zero times (`N = 0`, `rem = 20`), so `keccakAbsorbCursor inputBase 0`
    *is* `inputBase`, and `zkvm_keccak256_spec_within`'s
    `hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0` reduces to exactly
    this `decide`.

    ⛔ The contrast that matters: `bal_account_path` hashes **in place at
    `item + 2`**, and `8 ∤ 2` makes the very same premise *provably false*, so
    a triple taken under it would cover no real input.  The obstruction is not
    "there is a keccak call" — it is where the hashed slab sits. -/
theorem wtpdKeccakSeamAligned : (WS + (16 : Word)).toNat % 8 = 0 := by decide

#print axioms wtpdKeccakSeamAligned

/-- The output-window byte accesses `withdrawal_decode` asks its caller to
    guarantee, discharged statically: the 20 address bytes at
    `wtpd_struct + 16` all land in `[RAM_MEM_START, RAM_MEM_END]`. -/
theorem wtpdStructAddrValid :
    ∀ k, k < 20 → isValidByteAccess ((WS + (16 : Word)) + BitVec.ofNat 64 k) = true := by
  intro k hk
  interval_cases k <;> decide

#print axioms wtpdStructAddrValid

/-! ## ⭐ The whole-routine failure-arm contract -/

/-- ⭐ **The gated callee step**, lifted to top level.

    `withdrawal_decode_spec_within` instantiated at this routine's frame
    (`sp0 = sp - 32`, `spW = sp - 64`, return address `WTPD + 36`) with
    `wtpd_struct` as the output struct, and its two-way post collapsed onto the
    FAILURE disjunct by the gate `hnodec`.

    ⚠️ Both assertions are written in the order their sources produce them —
    the pre is `withdrawal_decode`'s own pre with the link register hoisted for
    `WP.cpsCallWithin`, the post is `wdCommon ;; wdScratch ;; cells` flattened.
    That is not cosmetic: `xperm` is worst-case in the size of the permutation
    it has to find, and on a 36-atom footprint an arbitrary reordering makes it
    give up — silently, emitting `sorryAx` rather than an error. Keeping both
    permutations near-identity is what makes this step check. -/
theorem wtpdDecodeFailStep
    (sp listBase len v12 v13 v14 v18 s3 s4 s5 : Word)
    (oldOut0 fld1Out oldOut2 oldOffset0 oldLen0 wOldOff wOldLen : Word)
    (bytes oldAddr pad4 : List (BitVec 8)) (listLen : Nat)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hbytes : listLen ≤ bytes.length)
    (hnowrap : listBase.toNat + listLen + 9 < 2 ^ 64)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnz : 0 < bytes.length)
    (haddrlen : oldAddr.length = 20)
    (hnodec : ∀ v0 v1 v3 o2 l2,
      ¬ WithdrawalDecodeSpec.Decoded bytes listBase listLen v0 v1 v3 o2 l2) :
    cpsTripleWithin wdDecodeFuel WithdrawalDecodeSpec.WB (WTPD + (36 : Word))
      WithdrawalDecodeSpec.fullCode
      ((.x1 ↦ᵣ (WTPD + (36 : Word))) **
       (EvmAsm.Rv64.SAsm.stackFree (sp - (64 : Word)) 12 **
        (.x2 ↦ᵣ (sp - (32 : Word))) ** (.x8 ↦ᵣ v12) ** (.x9 ↦ᵣ v13) **
        (.x18 ↦ᵣ v18) ** (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ len) ** (.x12 ↦ᵣ WS) **
        (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
        (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) **
        memOwn (sp - (64 : Word)) ** memOwn (sp - (56 : Word)) **
        memOwn (sp - (48 : Word)) ** memOwn (sp - (40 : Word)) **
        bytesRegion listBase bytes **
        (WS ↦ₘ oldOut0) ** ((WS + 8) ↦ₘ fld1Out) **
        bytesRegion (WS + 16) oldAddr ** bytesRegion (WS + 36) pad4 **
        ((WS + 40) ↦ₘ oldOut2) **
        (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.offsetCell ↦ₘ oldOffset0) **
        (EvmAsm.Codegen.RlpFieldToU64StrictSAsm.lengthCell ↦ₘ oldLen0) **
        (WithdrawalDecodeSpec.wdOffsetAddr ↦ₘ wOldOff) **
        (WithdrawalDecodeSpec.wdLengthAddr ↦ₘ wOldLen)))
      ((.x10 ↦ᵣ (1 : Word)) **
       (.x2 ↦ᵣ (sp - (32 : Word))) ** (.x1 ↦ᵣ (WTPD + (36 : Word))) **
       (.x8 ↦ᵣ v12) ** (.x9 ↦ᵣ v13) ** (.x18 ↦ᵣ v18) **
       ((sp - (64 : Word)) ↦ₘ (WTPD + (36 : Word))) **
       ((sp - (56 : Word)) ↦ₘ v12) ** ((sp - (48 : Word)) ↦ₘ v13) **
       ((sp - (40 : Word)) ↦ₘ v18) **
       (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       (.x0 ↦ᵣ (0 : Word)) **
       wtpdFailCells (sp - (64 : Word)) WS listBase bytes) := by
  have hU0 := WithdrawalDecodeSpec.withdrawal_decode_spec_within
    (sp - (32 : Word)) (sp - (64 : Word)) (sp - (96 : Word)) (WTPD + (36 : Word))
    v12 v13 v18 listBase len WS v13 v14 oldOut0 oldOffset0 oldLen0 fld1Out oldOut2
    wOldOff wOldLen s3 s4 s5 bytes oldAddr pad4 listLen
    (by rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide]; bv_omega)
    (by rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide]; bv_omega)
    (by decide) hlenW hsalign hbytes hnowrap hover hvalid hnz
    (by decide) (by decide) haddrlen wtpdStructAddrValid
  -- normalise the callee's frame-slot addresses to this routine's `sp - N` form
  rw [show (sp - (64 : Word)) + 8 = sp - (56 : Word) from by bv_omega,
      show (sp - (64 : Word)) + 16 = sp - (48 : Word) from by bv_omega,
      show (sp - (64 : Word)) + 24 = sp - (40 : Word) from by bv_omega] at hU0
  -- reshape into the call adapter's `(.x1 ↦ᵣ ret) ** Prest` shape, and collapse
  -- the callee's two-way post onto its failure disjunct using the gate
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hU0
  rcases hq with ⟨v0, v1, v3, o2, l2, hL⟩ | hR
  · exact absurd ((sepConj_pure_left h).mp hL).1 (hnodec v0 v1 v3 o2 l2)
  · have hR2 := (sepConj_pure_left h).mp hR
    obtain ⟨ha, hb, hd1, hu1, hx10, hrest⟩ := hR2.2
    obtain ⟨hc, hdd, hd2, hu2, hcom, hlft⟩ := hrest
    have hlft' := wdFailLeftover_split (sp - (64 : Word)) WS listBase s3 s4 s5
      bytes hdd hlft
    have hall : ((.x10 ↦ᵣ (1 : Word)) **
        WithdrawalDecodeSpec.wdCommon (sp - (32 : Word)) (sp - (64 : Word))
          (WTPD + (36 : Word)) v12 v13 v18 **
        WithdrawalDecodeSpec.wdScratch s3 s4 s5 **
        wtpdFailCells (sp - (64 : Word)) WS listBase bytes) h :=
      ⟨ha, hb, hd1, hu1, hx10, hc, hdd, hd2, hu2, hcom, hlft'⟩
    unfold WithdrawalDecodeSpec.wdCommon WithdrawalDecodeSpec.wdScratch at hall
    rw [show (sp - (64 : Word)) + 8 = sp - (56 : Word) from by bv_omega,
        show (sp - (64 : Word)) + 16 = sp - (48 : Word) from by bv_omega,
        show (sp - (64 : Word)) + 24 = sp - (40 : Word) from by bv_omega] at hall
    xperm_hyp hall

#print axioms wtpdDecodeFailStep

/-! ## ⛔ The whole-routine triple is NOT closed here — and why

    Everything above composes.  What does not go through is the final assembly

        segment A  ;;  the gated call  ;;  segment B  ;;  segment C

    and the obstruction is in `seqFrame`/`xperm`, not in the routine (#13207).

    `xperm_hyp h` expands to `exact (congrFun (show _ = _ by xperm) _).mp h`
    (`riscv-zkvm/…/Tactics/XSimp.lean:34`), and `xperm` has to *find* the
    permutation relating the two `**` chains.  On this routine the footprint is
    **36 atoms** — `withdrawal_decode`'s precondition is large (a 12-cell scratch
    stack, four save slots, fourteen registers, seven `regOwn`s, the input
    region, five output-struct pieces and four RLP data cells) — and beyond some
    distance `xperm` gives up.

    ⛔ **It gives up SILENTLY, by emitting `sorryAx`, not by reporting an error.**
    That is the trap worth recording.  The visible symptom is a cascade of
    "don't know how to synthesize placeholder" attributed to *every* `have` in
    the tactic block, with the main goal shown; there is no message naming
    `xperm`, and `#print axioms` is the only thing that tells the truth.
    `seqFrame` inherits the same behaviour: its `assignOrPermuteWithin` path
    (`riscv-zkvm/…/Tactics/SeqFrame.lean:1012`) calls `replaceMainGoal []` on
    success, so a permutation that "succeeds" with a sorry inside leaves an
    empty goal list and a tainted proof, and a following tactic reports
    "No goals to be solved" rather than anything diagnostic.

    Distance, not size, is what matters: `wtpdDecodeFailStep` above performs
    **two** 36-atom permutations and is clean (classical-3 only), because both
    were deliberately written near-identity — the precondition in
    `withdrawal_decode_spec_within`'s own order with only the link register
    hoisted, the postcondition as `wdCommon ;; wdScratch ;; cells` flattened in
    place.  The four-way assembly cannot be arranged that way: segment A's
    postcondition order is fixed by the prologue's instruction order and does
    not align with the callee's precondition order, so `seqFrame` is asked for a
    genuinely long permutation.

    Closing the row therefore needs one of:

      * an `xperm` that is complete (or that fails loudly) on ~40 atoms; or
      * a `seqFrame` variant that takes the atom correspondence explicitly; or
      * bundling `withdrawal_decode`'s precondition behind a single opaque
        `def` (as `wtpdFailCells` already does for its postcondition), which
        would cut the visible atom count at the seam from 36 to about 10.

    The third is the cheapest and is what the next attempt should do. -/

/-! ## Non-vacuity of the gate

  `notDecoded_of_noStrictList` is only worth anything if its premise is
  satisfiable AND is a real restriction.  Both directions are exhibited, and
  the second one is the load-bearing half: the gate has to be provably FALSE
  somewhere, or it would be framing dressed up as a hypothesis. -/

/-- **Satisfiable instance.**  Two zero bytes are not a strict RLP list —
    `StrictListPayload`'s two constructors both require `bytes[0] ≥ 0xc0`
    (`short` via `hlist`, `long` via `hlong`) — so no assignment of the four
    field values makes them a `Decoded` withdrawal, for any declared length. -/
example (base : Word) (listLen : Nat) :
    ∀ v0 v1 v3 o2 l2,
      ¬ WithdrawalDecodeSpec.Decoded (List.replicate 2 (0 : BitVec 8)) base listLen
        v0 v1 v3 o2 l2 :=
  notDecoded_of_noStrictList _ base listLen (by
    rintro ⟨cursorOff, endPtr, h⟩
    cases h with
    | short b hbyte hlist _ _ _ =>
        have hb : (0 : BitVec 8) = b := by simpa using hbyte
        exact hlist (by rw [← hb]; decide)
    | long b _ hbyte hlong _ _ _ _ _ =>
        have hb : (0 : BitVec 8) = b := by simpa using hbyte
        exact hlong (by rw [← hb]; decide))

/-- ⛔ **Negative control — the gate is provably FALSE here.**  A leading
    `0xc4` IS a short-form strict list header, so `StrictListPayload` holds and
    `notDecoded_of_noStrictList`'s premise is refuted outright.  The gate is
    therefore a genuine restriction on the input, not a fact about every input,
    and the `[0x00, 0x00]` witness above is not proving something vacuous. -/
example (base : Word) :
    ∃ cursorOff endPtr,
      EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload
        [(0xc4 : BitVec 8), 0, 0, 0, 0] base 5 cursorOff endPtr :=
  ⟨1, base + BitVec.ofNat 64 5,
    .short 5 1 (0xc4 : BitVec 8) (by decide) (by decide) (by decide) rfl (by decide)⟩

/-- ⛔ **Second control, on the arm the gate selects.**  `withdrawal_decode`'s
    post is a two-way disjunction and the gate picks the right one; the two
    arms are distinguishable exactly because the answers differ, which is what
    makes the `bnez a0` at index 9 decidable. -/
example : (1 : Word) ≠ (0 : Word) := by decide


end EvmAsm.Codegen.Proofs
