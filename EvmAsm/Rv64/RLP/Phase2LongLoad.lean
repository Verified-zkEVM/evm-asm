/-
  EvmAsm.Rv64.RLP.Phase2LongLoad

  EL.3 Phase 2 (long form) — load-and-accumulate step.

  Composes the byte load (`LBU`) with the two-instruction arithmetic
  accumulator `rlp_phase2_long_acc_prog` into a 3-instruction body that
  reads one byte from memory and folds it into the running length:

      LBU  x12, x13, 0        ; byte = mem[x13]
      SLLI x11, x11, 8        ; length <<= 8
      ADD  x11, x11, x12      ; length += byte

  This is one tick of the long-form length-of-length loop, minus the
  pointer / counter advance and the branch back. Layered on top of the
  arithmetic-only spec in `Phase2LongAcc.lean`.

  Register usage:
    x11 — accumulated length (mutated)
    x12 — scratch byte slot (mutated to hold the loaded byte)
    x13 — byte pointer (preserved; the caller advances it separately)
-/

-- `Phase2LongAcc → SyscallSpecs → ByteOps`.
import EvmAsm.Rv64.RLP.Phase2LongAcc
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Program definition
-- ============================================================================

/-- Three-instruction load-and-accumulate step:
    `LBU x12, x13, 0 ; SLLI x11, x11, 8 ; ADD x11, x11, x12`. -/
def rlp_phase2_long_load_acc_prog : Program :=
  (.LBU .x12 .x13 0) :: rlp_phase2_long_acc_prog

example : rlp_phase2_long_load_acc_prog.length = 3 := rfl

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post: `x11` holds `(len <<< 8) + byteZext`, `x12` holds the
    loaded byte (zero-extended to 64 bits), `x13` and memory are unchanged.

    `byteZext` is parametric — the caller supplies the concrete byte
    value extracted from the containing doubleword. Wrapped
    `@[irreducible]` to keep the let-bindings out of the theorem statement. -/
@[irreducible]
def rlp_phase2_long_load_acc_post
    (len ptr byteZext wordVal dwordAddr : Word) : Assertion :=
  let length' := (len <<< 8) + byteZext
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr) ** (.x12 ↦ᵣ byteZext) **
    (dwordAddr ↦ₘ wordVal)

theorem rlp_phase2_long_load_acc_post_unfold
    (len ptr byteZext wordVal dwordAddr : Word) :
    rlp_phase2_long_load_acc_post len ptr byteZext wordVal dwordAddr =
    ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ ptr) **
     (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ wordVal)) := by
  delta rlp_phase2_long_load_acc_post; rfl

/-- `cpsTripleWithin` spec for the load-and-accumulate step.

    The caller owns the doubleword at `dwordAddr` containing the byte at
    `ptr` (established via `halign`, `hvalid`). After execution, `x11`
    holds `len * 256 + byte` (as BitVec arithmetic) and `x12` holds the
    zero-extended byte. `x13` and memory are preserved. -/
theorem rlp_phase2_long_load_acc_spec_within (len ptr v12Old wordVal dwordAddr : Word)
    (base : Word)
    (halign : alignToDword ptr = dwordAddr)
    (hvalid : isValidByteAccess ptr = true) :
    let byteZext := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase2_long_load_acc_prog)
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x12 ↦ᵣ v12Old) **
       (dwordAddr ↦ₘ wordVal))
      (rlp_phase2_long_load_acc_post len ptr byteZext wordVal dwordAddr) := by
  simp only [rlp_phase2_long_load_acc_post_unfold]
  -- Reshape the top-level CodeReq: `ofProg base (LBU :: acc_prog)` unfolds
  -- to `singleton base LBU ∪ ofProg (base + 4) acc_prog`.
  have hcr_eq : CodeReq.ofProg base rlp_phase2_long_load_acc_prog =
      (CodeReq.singleton base (.LBU .x12 .x13 0)).union
      (CodeReq.ofProg (base + 4) rlp_phase2_long_acc_prog) := by
    simp only [rlp_phase2_long_load_acc_prog, CodeReq.ofProg_cons]
  rw [hcr_eq]
  -- Disjointness: the singleton at `base` is outside the acc program's
  -- 8-byte range `[base + 4, base + 12)`.
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      (CodeReq.ofProg (base + 4) rlp_phase2_long_acc_prog) := by
    apply CodeReq.Disjoint.singleton_ofProg
    apply CodeReq.ofProg_none_range
    intro k hk
    simp only [rlp_phase2_long_acc_prog, List.length_cons, List.length_nil] at hk
    interval_cases k <;> bv_omega
  -- Step 1: LBU x12, x13, 0. `signExtend12 0 = 0`, so `ptr + 0 = ptr`.
  have hptr_eq : ptr + signExtend12 (0 : BitVec 12) = ptr := by
    show ptr + (0 : Word) = ptr; bv_omega
  have halign' : alignToDword (ptr + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [hptr_eq]; exact halign
  have hvalid' : isValidByteAccess (ptr + signExtend12 (0 : BitVec 12)) = true := by
    rw [hptr_eq]; exact hvalid
  have lbu := generic_lbu_spec_within .x12 .x13 ptr v12Old 0 base dwordAddr wordVal
    (by nofun) halign' hvalid'
  rw [hptr_eq] at lbu
  -- Frame LBU with `x11 ↦ᵣ len` and permute to match the sequence shape.
  let byteZext := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  have lbu_framed : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU .x12 .x13 0))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x12 ↦ᵣ v12Old) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x12 ↦ᵣ byteZext) **
       (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x11 ↦ᵣ len) (by pcFree) lbu)
  -- Step 2: accumulation step at `base + 4`. Frame with `x13` and memory.
  have acc := rlp_phase2_long_acc_spec_within len byteZext (base + 4)
  simp only [rlp_phase2_long_acc_post_unfold] at acc
  rw [show (base + 4 : Word) + 8 = base + 12 from by bv_omega] at acc
  have acc_framed : cpsTripleWithin 2 (base + 4) (base + 12)
      (CodeReq.ofProg (base + 4) rlp_phase2_long_acc_prog)
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x12 ↦ᵣ byteZext) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) ** (.x13 ↦ᵣ ptr) **
       (.x12 ↦ᵣ byteZext) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x13 ↦ᵣ ptr) ** (dwordAddr ↦ₘ wordVal)) (by pcFree) acc)
  exact cpsTripleWithin_seq hd lbu_framed acc_framed

end EvmAsm.Rv64.RLP
