/-
  EvmAsm.Codegen.Programs.BloomOrIntoBridge

  GH #11348 — the last link. Both halves of this issue already existed and neither
  could see the other:

    * guest side, `BloomOrIntoSAsm.lean` — `bloomOrIntoFn_spec`, the loop's post
      given as `orWin src orig 32`, i.e. `(List.range 256).map (orByte src orig)`;
    * reference side, `SpecRef/BloomAlgebra.lean` — `bloomOr`, plus the fact that
      makes it load-bearing, `logs_bloom_append`.

  ⭐ THE POINT. The guest's post is *definitionally* the reference `bloomOr` —
  `orByte src orig k` and `bloomOr orig src`'s mapped function are the same term up
  to eta. That is not luck: `bloomOr` was deliberately written in the guest's
  `(List.range 256).map` shape rather than the `List.set`-fold shape `add_to_bloom`
  uses, precisely so this bridge would be `rfl` and the *interesting* content would
  live where it belongs — in `BloomAlgebra`'s proof that `logs_bloom` decomposes
  along `bloomOr` at all (that is where the byte-collision case analysis sits).

  ⚠️ ARGUMENT ORDER is the one place to be careful. The routine computes
  `dst |= src` in place, so the guest's `orig` is the **destination** (accumulator)
  and `src` is the incoming bloom. Under `bloomOr` that is `bloomOr orig src` —
  operands swapped relative to the guest's `(src, orig)` parameter order. `bloomOr`
  is commutative in fact, but nothing here relies on that.

  SCOPE, per `docs/leaf-routine-targets.md:46` and the issue: the **fold** only.
  The per-log index derivation (`keccak256` + the 11-bit extraction) is out of
  scope for #11348 and enters only as an opaque function of the log entry.
-/

import EvmAsm.Codegen.Programs.BloomOrIntoSAsm
import EvmAsm.Stateless.SpecRef.BloomAlgebra

namespace EvmAsm.Codegen.BloomOrIntoSAsm

open EvmAsm.Stateless.SpecRef

/-- ⭐ **The bridge.** The window the guest loop leaves behind after all 32 dwords
    is exactly the reference pointwise OR of the destination with the source.

    Note the operand swap: the guest's `orig` is the accumulator (`dst`), so it is
    `bloomOr`'s *first* argument. -/
theorem orWin_full_eq_bloomOr (src orig : List (BitVec 8)) (h : orig.length = 256) :
    orWin src orig 32 = bloomOr orig src := by
  rw [orWin_full src orig h, bloomOr]
  rfl

/-- The same statement in the `orByte`-map form `bloomOrIntoFn_spec` exposes, for
    callers that have already rewritten with `orWin_full`. -/
theorem map_orByte_eq_bloomOr (src orig : List (BitVec 8)) :
    (List.range 256).map (orByte src orig) = bloomOr orig src := by
  rw [bloomOr]; rfl

/-- ⭐ **Why the guest is allowed to accumulate per receipt at all.**

    The reference `logs_bloom` takes the block's logs as one flat list; the guest
    instead computes a bloom per receipt and ORs them together with this routine.
    Those two strategies agree — and this is the theorem that says so, obtained by
    composing the bridge above with `BloomAlgebra.logs_bloom_append`.

    Read it as: running `bloom_or_into` with `dst = logs_bloom l₁` and
    `src = logs_bloom l₂` leaves `dst = logs_bloom (l₁ ++ l₂)`. Induction over the
    receipt list then lifts it to a whole block. -/
theorem bloomOrInto_accumulates_logs_bloom (l₁ l₂ : List Log) :
    orWin (logs_bloom l₂) (logs_bloom l₁) 32 = logs_bloom (l₁ ++ l₂) := by
  rw [orWin_full_eq_bloomOr _ _ (logs_bloom_length l₁), ← logs_bloom_append]

/-- The block-level lift: folding the routine over a list of per-receipt log
    groups, seeded at the zero bloom, computes the bloom of all the logs.

    This is the shape the block builder actually runs. -/
theorem bloomOrInto_fold_eq_logs_bloom (groups : List (List Log)) :
    groups.foldl (fun acc g => bloomOr acc (logs_bloom g)) zeroBloom
      = logs_bloom groups.flatten := by
  -- ⚠️ `simp [logs_bloom]` loops here (`logs_bloom.eq_1` against
  -- `List.reduceReplicate`), so both cases stay on targeted rewrites.
  induction groups using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.foldl_append, ih, List.flatten_append, logs_bloom_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl

end EvmAsm.Codegen.BloomOrIntoSAsm
