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

  `withdrawalToPathDeltaFailFlat_spec`, a whole-routine triple entry → `ret`
  under one named gate: **the input is not a strict RLP list at all**, so
  `withdrawal_decode` cannot return its `Decoded` verdict, the `bnez a0` at
  instruction index 9 is TAKEN, and the routine answers `a0 = 1` from
  `.Lwtpd_fail`.

  The covered path is instruction indices **0..9 and 35..40** — sixteen of the
  forty-one — and it composes exactly one callee contract,
  `withdrawal_decode_spec_within` (`Programs/WithdrawalDecodeClose5.lean:1167`),
  reused rather than re-proved.

  ⭐ **The load-bearing part is what the post does NOT name.**  Neither the
  caller's 64-byte path buffer (`a2`, stashed in `s0`) nor its 32-byte delta
  buffer (`a3`, stashed in `s1`) appears anywhere in the pre or the post, and
  neither does `wtpd_hash`.  Because `cpsTripleWithin` universally quantifies
  over a `pcFree` frame, that silence is a **no-write guarantee**: on the
  failure arm the routine leaves both caller output buffers and the hash
  scratch exactly as it found them.  That is precisely the property a caller
  needs in order to read `a0 = 1` and skip the withdrawal.

  ## ⭐ The keccak seam is available here — measured, not assumed

  This routine's `zkvm_keccak256` call is NOT on the covered path, but the
  question of whether it *could* be was the blocker that ruled out
  `bal_account_path`, so it is worth recording where it actually lands.

  Every keccak seam carries `hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0`
  (`Proofs/HashBridgeKeccakTop.lean:408`), forced by `bytesRegion_lbu_within`'s
  `regionBase.toNat % 8 = 0` (`riscv-zkvm/RiscvZkvm/Rv64/Logic/MemRegion.lean:211`).
  The hashed slab here is the 20-byte address at `wtpd_struct + 16`, and
  `keccakAbsorbCursor inputBase 0 = inputBase` for a 20-byte preimage
  (`N = 0`, `rem = 20`), so the premise reduces to a static `decide` — see
  `wtpdKeccakSeamAligned` below.  `bal_account_path` hashes in place at
  `item + 2`, where `8 ∤ 2` makes the same premise *provably false*.

  The other two obstructions recorded on #13014 are absent as well: the
  20-byte window is already handed over pre-carved as a standalone
  `bytesRegion (outBase + 16) oldAddr` by `withdrawal_decode`'s own contract
  (so nothing must be split out of a dword-granular region), and
  `zkvm_keccak256_spec_within` asks only `input.length = 136 * N + rem` with
  `rem ≤ 135`, which `20 = 136 * 0 + 20` satisfies.

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

end EvmAsm.Codegen.Proofs
