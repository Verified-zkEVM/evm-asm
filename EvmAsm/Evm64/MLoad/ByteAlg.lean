/-
  EvmAsm.Evm64.MLoad.ByteAlg

  Pure Word-level identity used by the upcoming MLOAD per-limb spec
  (`docs/99-mload-design.md` §6 sub-slice 3b, beads `evm-asm-md9l`).

  The MLOAD per-limb byte-pack (§3.2 of the design) processes bytes
  big-endian: starting from accumulator `0`, repeatedly `(acc <<< 8) ||| b_i`
  for `i = 7, 6, …, 0`. The final 64-bit accumulator equals
  `b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0` — i.e. the eight bytes
  concatenated in big-endian order (b7 in the high 8 bits, b0 in the
  low 8 bits).

  This file exposes that identity as `bytePack8_eq`, decided by
  `bv_decide`. Standalone — no dependence on machine state, separation
  logic, or the Program. Consumed by sub-slice 3d
  (`mload_one_limb_spec_within`) when bridging the runtime
  shift-OR accumulator to the static 64-bit value asserted by the
  per-limb postcondition.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/
import EvmAsm.Rv64.Basic
import Std.Tactic.BVDecide

namespace EvmAsm.Evm64.MLoad

/--
  Big-endian byte-pack identity for 8 bytes into a single 64-bit limb.

  This matches the runtime shape produced by the MLOAD per-limb pack
  loop in `EvmAsm/Evm64/MLoad/Program.lean`: the accumulator starts at
  `0`, the most-significant byte (`b7`) is loaded first, and each
  subsequent byte is folded in via `(acc <<< 8) ||| b_k.zeroExtend 64`.

  After 8 iterations, the accumulator equals the big-endian
  concatenation `b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0` (where
  `BitVec.append` places its first argument in the high bits).
-/
theorem bytePack8_eq (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((((((((b7.zeroExtend 64
        <<< (8 : Nat)) ||| b6.zeroExtend 64)
        <<< (8 : Nat)) ||| b5.zeroExtend 64)
        <<< (8 : Nat)) ||| b4.zeroExtend 64)
        <<< (8 : Nat)) ||| b3.zeroExtend 64)
        <<< (8 : Nat)) ||| b2.zeroExtend 64)
        <<< (8 : Nat)) ||| b1.zeroExtend 64)
        <<< (8 : Nat)) ||| b0.zeroExtend 64)
      = b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  bv_decide

/--
  Variant of `bytePack8_eq` that explicitly threads the initial
  zero seed used by the runtime: `(0#64 <<< 8) ||| x = x.zeroExtend 64`
  reduces away, but recording the equation pre-reduction lets later
  proofs match the program's literal accumulator chain without
  manually unfolding the seed step.
-/
theorem bytePack8_eq_zero_seed (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (((((((((((((((((0 : Word)
        <<< (8 : Nat)) ||| b7.zeroExtend 64)
        <<< (8 : Nat)) ||| b6.zeroExtend 64)
        <<< (8 : Nat)) ||| b5.zeroExtend 64)
        <<< (8 : Nat)) ||| b4.zeroExtend 64)
        <<< (8 : Nat)) ||| b3.zeroExtend 64)
        <<< (8 : Nat)) ||| b2.zeroExtend 64)
        <<< (8 : Nat)) ||| b1.zeroExtend 64)
        <<< (8 : Nat)) ||| b0.zeroExtend 64)
      = b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  bv_decide

end EvmAsm.Evm64.MLoad
