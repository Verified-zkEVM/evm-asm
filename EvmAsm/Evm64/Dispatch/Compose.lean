/-
  EvmAsm.Evm64.Dispatch.Compose

  Slice 3d of GH #106 (parent `evm-asm-77w8s`, blocks slice 3
  `evm-asm-afkny`, this slice `evm-asm-ndswy`).

  Compose `evm_dispatch_entry_addr_spec_within` (slice 3b) with
  `evm_dispatch_tail_spec_within` (slice 3 tail) into a 5-step Hoare
  triple for the full `evm_dispatch` program.  This slice does **not**
  consume `dispatchTableIs_split` — instead it takes the table-entry
  cell `(tableBase + 8 * opcode) ↦ₘ handlerAddr` as an explicit
  hypothesis in both the precondition and postcondition.  Slice 3
  (`evm-asm-afkny`) wraps this lemma with `dispatchTableIs_split` to
  derive the full `dispatch_spec`.

  Strategy: frame the table-entry cell on EntrySpec; frame everything
  else (other registers + dword) on TailSpec; bridge the address forms
  via `entry_addr_bridge_fin`; compose with `cpsTripleWithin_seq`.

  The opcode byte is exposed by an explicit hypothesis
  `extractByte wordVal (byteOffset _) = BitVec.ofNat 8 opcode.val`,
  letting the proof rewrite EntrySpec's loaded byte (the
  `(extractByte ...).zeroExtend 64` form) to `BitVec.ofNat 64 opcode.val`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

module

public import EvmAsm.Evm64.Dispatch.EntrySpec
public import EvmAsm.Evm64.Dispatch.TailSpec
public import EvmAsm.Evm64.Dispatch.EntryAddrBridge

@[expose] public section

namespace EvmAsm.Evm64
namespace Dispatch

open EvmAsm.Rv64

/-- The dispatch program decomposes into the entry-address block
    (LBU+SLLI+ADD) at `base` and the tail block (LD+JALR) at `base + 12`. -/
theorem dispatch_codeReq_split (base : Word) :
    CodeReq.ofProg base evm_dispatch
      = (entryAddrCode base).union (tailCode (base + 12)) := by
  -- Both sides reduce to a chain of singletons; unfold and chase
  -- `ofProg_cons`/`ofProg_nil`.
  show CodeReq.ofProg base
        [.LBU rOp rOpPtr opcodeLbuOff, .SLLI rOp rOp entryShiftAmt,
         .ADD rOp rOp rTable, .LD rOp rOp handlerLdOff,
         .JALR .x0 rOp handlerJumpOff] = _
  unfold entryAddrCode tailCode
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil,
             CodeReq.union_empty_right]
  rw [show (base + 4 + 4 : Word) = base + 8 from by bv_omega,
      show (base + 8 + 4 : Word) = base + 12 from by bv_omega,
      show (base + 12 + 4 : Word) = base + 16 from by bv_omega]
  rw [CodeReq.union_assoc, CodeReq.union_assoc]

/-- Disjointness of the entry and tail blocks: one is at `[base, base+12)`,
    the other at `[base+12, base+20)`. -/
theorem entryAddrCode_tailCode_disjoint (base : Word) :
    (entryAddrCode base).Disjoint (tailCode (base + 12)) := by
  unfold entryAddrCode tailCode
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega]
  exact CodeReq.Disjoint.union_left
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega)))
    (CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega))))

/-- 5-step Hoare triple for `evm_dispatch`: from a frame holding the
    opcode dword, the table-entry cell, and the input registers, the
    program loads the handler address from the table and jumps to it.

    The opcode byte is identified via the hypothesis `h_opcByte`, which
    fixes the relevant byte of `wordVal` to be `BitVec.ofNat 8 opcode.val`.
    The table-entry cell is exposed as a separate atom — slice 3
    (`evm-asm-afkny`) will derive it from `dispatchTableIs_split`. -/
theorem evm_dispatch_compose_within
    (base pcAddr tableBase rOpInit wordVal dwordAddr handlerAddr : Word)
    (opcode : Fin 256)
    (h_align : alignToDword (pcAddr + signExtend12 opcodeLbuOff) = dwordAddr)
    (h_valid : isValidByteAccess (pcAddr + signExtend12 opcodeLbuOff) = true)
    (h_opcByte :
      extractByte wordVal (byteOffset (pcAddr + signExtend12 opcodeLbuOff))
        = BitVec.ofNat 8 opcode.val) :
    cpsTripleWithin 5 base
      ((handlerAddr + signExtend12 handlerJumpOff) &&& ~~~1)
      (CodeReq.ofProg base evm_dispatch)
      ((rOpPtr ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) **
        (rOp ↦ᵣ rOpInit) ** (dwordAddr ↦ₘ wordVal) **
        ((tableBase + BitVec.ofNat 64 (8 * opcode.val)) ↦ₘ handlerAddr))
      ((rOpPtr ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) **
        (rOp ↦ᵣ handlerAddr) ** (dwordAddr ↦ₘ wordVal) **
        ((tableBase + BitVec.ofNat 64 (8 * opcode.val)) ↦ₘ handlerAddr)) := by
  -- Step A: EntrySpec, simplified using h_opcByte.
  have E0 := evm_dispatch_entry_addr_spec_within base pcAddr tableBase rOpInit
              wordVal dwordAddr h_align h_valid
  simp only [h_opcByte] at E0
  -- The loaded opcode byte is now `(BitVec.ofNat 8 opcode.val).zeroExtend 64`,
  -- which equals `BitVec.ofNat 64 opcode.val`.
  have hZE : ((BitVec.ofNat 8 opcode.val).zeroExtend 64 : Word)
              = BitVec.ofNat 64 opcode.val := by
    apply BitVec.eq_of_toNat_eq
    have h64 : opcode.val < 2 ^ 64 := by have := opcode.isLt; omega
    have h8  : opcode.val < 2 ^ 8  := opcode.isLt
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [hZE] at E0
  -- Normalize the shift amount in EntrySpec output (entryShiftAmt.toNat = 3).
  have hShift : entryShiftAmt.toNat = 3 := by decide
  rw [hShift] at E0
  -- Bridge address form: `(BitVec.ofNat 64 opcode.val) <<< 3 + tableBase`
  -- = `tableBase + BitVec.ofNat 64 (8 * opcode.val)`.
  rw [entry_addr_bridge_fin tableBase opcode] at E0
  -- Frame the table-entry cell on EntrySpec.
  have E1 := cpsTripleWithin_frameR
    ((tableBase + BitVec.ofNat 64 (8 * opcode.val)) ↦ₘ handlerAddr)
    (by pcFree) E0
  -- Step B: TailSpec, instantiated at base + 12 with the right entry address.
  have T0 := evm_dispatch_tail_spec_within (base + 12)
              (tableBase + BitVec.ofNat 64 (8 * opcode.val))
              handlerAddr
  -- Frame the other registers + dword on TailSpec. We do this via
  -- `cpsTripleWithin_frameL`, treating those as the "rest" frame.
  have T1 := cpsTripleWithin_frameL
    ((rOpPtr ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) ** (dwordAddr ↦ₘ wordVal))
    (by pcFree) T0
  -- TailSpec entry uses `signExtend12 handlerLdOff = 0`, but it is left
  -- as `+ signExtend12 handlerLdOff`. Normalize.
  have hLd0 : signExtend12 handlerLdOff = (0 : Word) := by
    show signExtend12 (0 : BitVec 12) = (0 : Word); decide
  rw [hLd0] at T1
  rw [show (tableBase + BitVec.ofNat 64 (8 * opcode.val) + (0 : Word) : Word)
        = tableBase + BitVec.ofNat 64 (8 * opcode.val) from by bv_omega] at T1
  -- Compose with seq + perm: massage E1 post / T1 pre into matching shape.
  have hd : (entryAddrCode base).Disjoint (tailCode (base + 12)) :=
    entryAddrCode_tailCode_disjoint base
  -- Build the composed triple over `entryAddrCode base ∪ tailCode (base+12)`.
  have hcompose := cpsTripleWithin_seq_with_perm (P := _) (R := _) hd
    (Q1 :=
      ((rOpPtr ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) **
        (rOp ↦ᵣ tableBase + BitVec.ofNat 64 (8 * opcode.val)) **
        (dwordAddr ↦ₘ wordVal)) **
      ((tableBase + BitVec.ofNat 64 (8 * opcode.val)) ↦ₘ handlerAddr))
    (Q2 :=
      ((rOpPtr ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) ** (dwordAddr ↦ₘ wordVal))
      ** ((rOp ↦ᵣ tableBase + BitVec.ofNat 64 (8 * opcode.val)) **
          ((tableBase + BitVec.ofNat 64 (8 * opcode.val)) ↦ₘ handlerAddr)))
    (fun h hp => by xperm_hyp hp) E1 T1
  -- Now reshape: rewrite the CodeReq, then fix the entry/exit and
  -- pre/post into the goal's shape.
  rw [← dispatch_codeReq_split] at hcompose
  -- Step bound: 3 + 2 = 5.
  show cpsTripleWithin 5 base _ _ _ _
  -- Massage entry/exit and pre/post via weakening + permutation.
  -- The composed triple gives a postcondition shaped like T1's post
  -- ((rOpPtr** rTable ** dwordAddr) ** ((rOp ↦ handlerAddr) ** cell)).
  -- The goal wants `rOpPtr ** rTable ** rOp ** dwordAddr ** cell`.
  refine cpsTripleWithin_weaken (Q := _) (P := _) ?_ ?_ hcompose
  · intro h hp; xperm_hyp hp
  · intro h hp; xperm_hyp hp

end Dispatch
end EvmAsm.Evm64
