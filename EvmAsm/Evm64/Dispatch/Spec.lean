/-
  EvmAsm.Evm64.Dispatch.Spec

  Slice 3 of GH #106 (parent `evm-asm-77w8s`, this slice
  `evm-asm-afkny`).  Top-level Hoare triple `dispatch_spec` for the
  full RV64 dispatch sequence (`evm_dispatch`, slice 2), expressed
  against the full `dispatchTableIs` jump-table layout rather than
  the explicit entry cell exposed by slice 3d
  (`evm_dispatch_compose_within`).

  Strategy: wrap `evm_dispatch_compose_within` (the 5-step Hoare
  triple over the entry cell) with `dispatchTableIs_split` and
  frame the residual `dispatchTableIs.rest` chain as a pcFree frame.
  The split lemma rewrites
    `dispatchTableIs base handlers`
       = `(entryCell) ** dispatchTableIs.rest base handlers opcode`,
  letting the rest live as an invariant frame across the dispatch.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
  Refs GH #106, beads `evm-asm-afkny`, parent `evm-asm-77w8s`.
-/

module

public import EvmAsm.Evm64.Dispatch.Compose
public import EvmAsm.Evm64.JumpTable

@[expose] public section

namespace EvmAsm.Evm64
namespace Dispatch

open EvmAsm.Rv64

/-- The auxiliary table builder is `pcFree`: it reduces to a
    `sepConj` chain of `↦ₘ` cells (or `empAssertion`), each of which
    is `pcFree`. Proved by induction on the residual `count`. -/
theorem pcFree_dispatchTableIs_aux
    (base : Word) (handlers : Fin 256 → Word) :
    ∀ (start count : Nat), (dispatchTableIs.aux base handlers start count).pcFree
  | _, 0 => by
      unfold dispatchTableIs.aux
      exact pcFree_emp
  | start, n + 1 => by
      unfold dispatchTableIs.aux
      by_cases h : start < 256
      · simp [h]
        exact pcFree_sepConj pcFree_memIs
          (pcFree_dispatchTableIs_aux base handlers (start + 1) n)
      · simp [h]
        exact pcFree_emp

/-- The residual `dispatchTableIs.rest` chain (everything except the
    selected entry) is `pcFree`. -/
theorem pcFree_dispatchTableIs_rest
    (base : Word) (handlers : Fin 256 → Word) (opcode : Fin 256) :
    (dispatchTableIs.rest base handlers opcode).pcFree := by
  unfold dispatchTableIs.rest
  exact pcFree_sepConj
    (pcFree_dispatchTableIs_aux base handlers 0 opcode.val)
    (pcFree_dispatchTableIs_aux base handlers (opcode.val + 1) (255 - opcode.val))

/-- **`dispatch_spec`** — top-level Hoare triple for the RV64 dispatch
    sequence against the full jump-table layout.

    Given:
    * the dispatch input frame (`rOpPtr` at the opcode pointer,
      `rTable` at the jump-table base, `rOp` scratch),
    * the source dword carrying the opcode byte,
    * the entire `dispatchTableIs` layout at `tableBase`,
    * a hypothesis fixing the byte at the opcode pointer to
      `BitVec.ofNat 8 opcode.val`,

    five steps of execution leave control at the handler address
    `handlers opcode &&& ~~~1` with `rOp` holding the loaded handler
    address. The dword and the table are unchanged.

    The handler-address `&&& ~~~1` mask comes from `JALR`'s
    target-alignment rule (low bit cleared); `signExtend12 0 = 0`
    drops out of the JALR offset trivially. -/
theorem dispatch_spec
    (base pcAddr tableBase rOpInit wordVal dwordAddr : Word)
    (handlers : Fin 256 → Word) (opcode : Fin 256)
    (h_align : alignToDword (pcAddr + signExtend12 opcodeLbuOff) = dwordAddr)
    (h_valid : isValidByteAccess (pcAddr + signExtend12 opcodeLbuOff) = true)
    (h_opcByte :
      extractByte wordVal (byteOffset (pcAddr + signExtend12 opcodeLbuOff))
        = BitVec.ofNat 8 opcode.val) :
    cpsTripleWithin 5 base
      ((handlers opcode + signExtend12 handlerJumpOff) &&& ~~~1)
      (CodeReq.ofProg base evm_dispatch)
      ((rOpPtr ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) **
        (rOp ↦ᵣ rOpInit) ** (dwordAddr ↦ₘ wordVal) **
        dispatchTableIs tableBase handlers)
      ((rOpPtr ↦ᵣ pcAddr) ** (rTable ↦ᵣ tableBase) **
        (rOp ↦ᵣ handlers opcode) ** (dwordAddr ↦ₘ wordVal) **
        dispatchTableIs tableBase handlers) := by
  -- Step A: build the 5-step compose triple over the explicit entry cell.
  have hcompose := evm_dispatch_compose_within base pcAddr tableBase rOpInit
                    wordVal dwordAddr (handlers opcode) opcode
                    h_align h_valid h_opcByte
  -- Step B: frame `dispatchTableIs.rest` on top of the compose triple.
  have hframed := cpsTripleWithin_frameR
    (dispatchTableIs.rest tableBase handlers opcode)
    (pcFree_dispatchTableIs_rest tableBase handlers opcode)
    hcompose
  -- Step C: rewrite the entry cell + rest back into `dispatchTableIs` via
  -- `dispatchTableIs_split` (in reverse), then realign separation order.
  have hsplit := dispatchTableIs_split tableBase handlers opcode
  -- The compose pre/post is shaped as
  --   (rOpPtr ** rTable ** rOp ** dword ** entry) ** rest.
  -- The goal is shaped as
  --   rOpPtr ** rTable ** rOp ** dword ** dispatchTableIs.
  -- Permute and rewrite.
  refine cpsTripleWithin_weaken (P := _) (Q := _) ?_ ?_ hframed
  · -- Pre: goal ⇒ compose.pre. Rewrite dispatchTableIs in goal hypothesis
    --       into entry ** rest via hsplit, then xperm.
    intro h hp
    rw [hsplit] at hp
    xperm_hyp hp
  · -- Post: compose.post ⇒ goal. Same rewrite, opposite direction.
    intro h hp
    rw [hsplit]
    xperm_hyp hp

end Dispatch
end EvmAsm.Evm64
