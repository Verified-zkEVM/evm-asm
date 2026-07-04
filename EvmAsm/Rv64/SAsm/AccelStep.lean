/-
  EvmAsm.Rv64.SAsm.AccelStep

  The first machine-level CPS triple for a ZisK accelerator instruction
  (bead evm-asm-4ch8f.11, strategy in docs/4ch8f-crypto-strategy.md):
  a single `csrs 0x802, rs1` (Arith256Mod) step whose parameter block and
  operand buffers all live inside one SAsm writable window (`bytesRegion`).

  This file fixes the canonical accelerator-seam contract shape.  The SAsm
  block engine deliberately does not execute `CSRS` (`instrOk` rejects it);
  instead an accelerator step is admitted through the handle mechanism:
  a hand-proven `cpsTripleWithin` — established directly from `step_csrs`
  and the bead-`.1` concrete semantics (`csrsWrite`/`csrsValid`,
  ZiskAccel.lean) — is packaged as a snapshot-parameterized `FnHandleS`
  and invoked from SAsm code via `Stmt.callRegS`.  The pilot consumer is
  `EvmAsm.Rv64.SAsm.PowLadderDemo` (the MSB square-and-multiply ladder).

  Contents:
  - `wsDword` / `wsNat256` / `leBytes32`: window decode/encode helpers
    (little-endian, matching `Accel.leLimbsToNat`/`Accel.natToLeLimbs`).
  - `holdsFor_bytesRegion_readWords`: `MachineState.readWords` over a
    framed window reads the packed window dwords.
  - `holdsFor_bytesRegion_writeWords`: `MachineState.writeWords` into a
    framed window splices the payload bytes (the `execCsrs` update, at
    separation-logic granularity).
  - `csrs_arith256Mod_spec_within`: the one-step triple for
    `csrs 0x802, rs1` — output buffer := `(a·b + c) mod m` over the
    window-decoded operands.
  - `csrs_arith256Mod_ret_spec`: the triple with the `jalr x0, ra, 0`
    return epilogue, in exactly the `FnHandleS.sound` calling shape.
-/

import EvmAsm.Rv64.ZiskAccel
import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Window decode / encode helpers
-- ============================================================================

/-- The dword packed at byte offset `k` of a window. -/
def wsDword (ws : List (BitVec 8)) (k : Nat) : Word :=
  packBytes ((ws.drop k).take 8)

/-- The 256-bit little-endian natural at byte offset `k` of a window
    (4 LE u64 limbs — exactly what `Accel.arith256Mod` consumes through
    `Accel.leLimbsToNat ∘ MachineState.readWords`). -/
def wsNat256 (ws : List (BitVec 8)) (k : Nat) : Nat :=
  Accel.leLimbsToNat
    [wsDword ws k, wsDword ws (k + 8), wsDword ws (k + 16), wsDword ws (k + 24)]

/-- The 32-byte little-endian image of (the low 256 bits of) a natural —
    the byte-level view of `Accel.natToLeLimbs 4`. -/
def leBytes32 (v : Nat) : List (BitVec 8) :=
  (Accel.natToLeLimbs 4 v).flatMap dwordBytes

@[simp] theorem length_leBytes32 (v : Nat) : (leBytes32 v).length = 32 := by
  simp [leBytes32, Accel.natToLeLimbs, List.length_flatMap, Function.comp_def,
    length_dwordBytes]

-- ============================================================================
-- readWords over a framed window
-- ============================================================================

/-- `readWords` over a framed `bytesRegion` reads the packed window dwords. -/
theorem holdsFor_bytesRegion_readWords {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s) :
    ∀ (n k : Nat), 8 ∣ k → k + 8 * n ≤ bs.length →
      s.readWords (b + BitVec.ofNat 64 k) n
        = (List.range n).map (fun i => wsDword bs (k + 8 * i)) := by
  intro n
  induction n with
  | zero => intro k _ _; rfl
  | succ n ih =>
      intro k h8 hfit
      have hhead : s.getMem (b + BitVec.ofNat 64 k)
          = packBytes ((bs.drop k).take 8) :=
        holdsFor_bytesRegion_getMem hPR h8 (by omega)
      have haddr : (b + BitVec.ofNat 64 k) + 8 = b + BitVec.ofNat 64 (k + 8) := by
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have h8' : ((8 : BitVec 64)).toNat = 8 := by decide
        rw [h8']
        omega
      show s.getMem (b + BitVec.ofNat 64 k)
          :: s.readWords ((b + BitVec.ofNat 64 k) + 8) n = _
      rw [hhead, haddr, ih (k + 8) (by omega) (by omega),
        List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ List.cons ?_ (List.map_congr_left ?_)
      · show packBytes ((bs.drop k).take 8) = wsDword bs (k + 8 * 0)
        rw [show k + 8 * 0 = k from by omega]
        rfl
      · intro i _
        show wsDword bs (k + 8 + 8 * i) = wsDword bs (k + 8 * (i + 1))
        congr 1
        omega

-- ============================================================================
-- writeWords into a framed window
-- ============================================================================

/-- Splicing an appended payload = splicing the pieces in sequence. -/
theorem setBytes_append (xs ys bs : List (BitVec 8)) (k : Nat) :
    setBytes bs k (xs ++ ys) = setBytes (setBytes bs k xs) (k + xs.length) ys := by
  induction xs generalizing bs k with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append, setBytes_cons, List.length_cons]
      rw [ih]
      congr 1
      omega

/-- One aligned dword store into a framed window, at separation-logic
    granularity: the window's byte image gets the dword's bytes spliced in. -/
theorem holdsFor_bytesRegion_setMem_dword {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState} {k : Nat} (w : Word)
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    (h8 : 8 ∣ k) (hfit : k + 8 ≤ bs.length) :
    ((bytesRegion b (setBytes bs k (dwordBytes w))) ** R).holdsFor
      (s.setMem (b + BitVec.ofNat 64 k) w) := by
  obtain ⟨q, rfl⟩ := h8
  obtain ⟨front, rest, -, -, heq, heqset⟩ :=
    bytesRegion_dword_at_setBytes b bs (dwordBytes w) q 0
      (List.ne_nil_of_length_pos (by rw [length_dwordBytes]; omega))
      (by rw [length_dwordBytes]) (by rw [length_dwordBytes]; omega)
  rw [show 8 * q + 0 = 8 * q from by omega] at heqset
  rw [heq] at hPR
  rw [heqset]
  -- reassociate so the cell is at the head
  rw [sepConj_left_comm front _ rest, sepConj_assoc'] at hPR ⊢
  have hcell := holdsFor_sepConj_memIs_setMem
    (v' := packBytes (setBytes ((bs.drop (8 * q)).take 8) 0 (dwordBytes w)))
    hPR
  rw [← packBytes_setBytes_dword ((bs.drop (8 * q)).take 8) w
    (by rw [List.length_take, List.length_drop]; omega)] at hcell
  rw [← packBytes_setBytes_dword ((bs.drop (8 * q)).take 8) w
    (by rw [List.length_take, List.length_drop]; omega)]
  exact hcell

/-- `writeWords` into a framed window splices the payload's bytes: the
    separation-logic image of `execCsrs`'s single memory effect. -/
theorem holdsFor_bytesRegion_writeWords {b : Word} {R : Assertion} :
    ∀ (payload : List Word) (bs : List (BitVec 8)) (s : MachineState) (k : Nat),
      ((bytesRegion b bs) ** R).holdsFor s → 8 ∣ k →
      k + 8 * payload.length ≤ bs.length →
      ((bytesRegion b (setBytes bs k (payload.flatMap dwordBytes))) ** R).holdsFor
        (s.writeWords (b + BitVec.ofNat 64 k) payload) := by
  intro payload
  induction payload with
  | nil => intro bs s k hPR _ _; simpa using hPR
  | cons w rest ih =>
      intro bs s k hPR h8 hfit
      simp only [List.length_cons] at hfit
      have h1 := holdsFor_bytesRegion_setMem_dword w hPR h8 (by omega)
      have haddr : (b + BitVec.ofNat 64 k) + 8 = b + BitVec.ofNat 64 (k + 8) := by
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have h8' : ((8 : BitVec 64)).toNat = 8 := by decide
        rw [h8']
        omega
      show ((bytesRegion b _) ** R).holdsFor
        ((s.setMem (b + BitVec.ofNat 64 k) w).writeWords
          ((b + BitVec.ofNat 64 k) + 8) rest)
      rw [haddr,
        show (w :: rest).flatMap dwordBytes
          = dwordBytes w ++ rest.flatMap dwordBytes from rfl,
        setBytes_append, length_dwordBytes]
      exact ih (setBytes bs k (dwordBytes w))
        (s.setMem (b + BitVec.ofNat 64 k) w) (k + 8) h1 (by omega)
        (by rw [length_setBytes]; omega)

-- ============================================================================
-- Address arithmetic helpers
-- ============================================================================

theorem add_ofNat_add (b : Word) (k j : Nat) :
    (b + BitVec.ofNat 64 k) + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (k + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- An in-window aligned offset is a valid dword access (window wf). -/
theorem isValidDwordAccess_of_window {b : Word} {len : Nat}
    (hb8 : b.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (b + BitVec.ofNat 64 j) = true)
    {k : Nat} (h8 : 8 ∣ k) (hk : k < len) :
    isValidDwordAccess (b + BitVec.ofNat 64 k) = true := by
  rw [isValidDwordAccess_eq, Bool.and_eq_true]
  refine ⟨hvalid k hk, ?_⟩
  simp only [isAligned8, beq_iff_eq]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- An operand block inside the window passes `validDwordRange`. -/
theorem validDwordRange_of_window {b : Word} {len : Nat}
    (hb8 : b.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (b + BitVec.ofNat 64 j) = true)
    {k n : Nat} (h8 : 8 ∣ k) (hfit : k + 8 * n ≤ len) :
    MachineState.validDwordRange (b + BitVec.ofNat 64 k) n = true := by
  unfold MachineState.validDwordRange
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [add_ofNat_add]
  exact isValidDwordAccess_of_window hb8 hvalid
    (by obtain ⟨q, rfl⟩ := h8; exact ⟨q + i, by omega⟩) (by omega)

@[simp] theorem length_natToLeLimbs (n v : Nat) :
    (Accel.natToLeLimbs n v).length = n := by
  simp [Accel.natToLeLimbs]

/-- Decode a 256-bit operand through `readWords`, as the window natural. -/
theorem holdsFor_bytesRegion_readNat256 {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {k : Nat} (h8 : 8 ∣ k) (hfit : k + 32 ≤ bs.length) :
    Accel.leLimbsToNat (s.readWords (b + BitVec.ofNat 64 k) 4) = wsNat256 bs k := by
  rw [holdsFor_bytesRegion_readWords hPR 4 k h8 (by omega)]
  show Accel.leLimbsToNat
    [wsDword bs (k + 8 * 0), wsDword bs (k + 8 * 1),
     wsDword bs (k + 8 * 2), wsDword bs (k + 8 * 3)] = _
  rw [show k + 8 * 0 = k from by omega, show k + 8 * 1 = k + 8 from by omega,
    show k + 8 * 2 = k + 16 from by omega, show k + 8 * 3 = k + 24 from by omega]
  rfl

-- ============================================================================
-- The Arith256Mod step triple
-- ============================================================================

/-- The `csrsValid` arm selected by CSR id `0x802` (definitional). -/
private theorem csrsValid_arith256 (s : MachineState) (rs1 : Reg) :
    s.csrsValid 0x802 rs1
      = (MachineState.validDwordRange (s.getReg rs1) 5 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1)) 4 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 8)) 4 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 16)) 4 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 24)) 4 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 32)) 4 &&
         !(Accel.leLimbsToNat
             (s.readWords (s.getMem (s.getReg rs1 + 24)) 4) == 0)) := rfl

/-- The `csrsWrite` arm selected by CSR id `0x802` (definitional). -/
private theorem csrsWrite_arith256 (s : MachineState) (rs1 : Reg) :
    s.csrsWrite 0x802 rs1
      = (s.getMem (s.getReg rs1 + 32), Accel.natToLeLimbs 4 (Accel.arith256Mod
          (Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1)) 4))
          (Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 8)) 4))
          (Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 16)) 4))
          (Accel.leLimbsToNat
            (s.readWords (s.getMem (s.getReg rs1 + 24)) 4)))) := rfl

/-- **The accelerator step, at separation-logic granularity** (the first
    machine-level CPS triple for a `CSRS` instruction).  One
    `csrs 0x802, rs1` (Arith256Mod), with `rs1` pointing at a
    `[a*, b*, c*, module*, d*]` parameter block whose five pointers all
    land inside the writable window at dword-aligned, 32-byte-fitting
    offsets: the output buffer becomes `(a·b + c) mod m` (LE limbs) and
    nothing else moves — not even a register.

    The operand offsets may alias arbitrarily (the ladder squares with
    `a = b = d = acc`); only the *decoded entry values* appear in the
    postcondition, which is what makes the contract usable under
    aliasing. -/
theorem csrs_arith256Mod_spec_within
    (base : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff aOff bOff cOff mOff dOff : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 40 ≤ len)
    (h8a : 8 ∣ aOff) (hafit : aOff + 32 ≤ len)
    (h8b : 8 ∣ bOff) (hbfit : bOff + 32 ≤ len)
    (h8c : 8 ∣ cOff) (hcfit : cOff + 32 ≤ len)
    (h8m : 8 ∣ mOff) (hmfit : mOff + 32 ≤ len)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 32 ≤ len)
    (hpa : wsDword ws pOff = B + BitVec.ofNat 64 aOff)
    (hpb : wsDword ws (pOff + 8) = B + BitVec.ofNat 64 bOff)
    (hpc : wsDword ws (pOff + 16) = B + BitVec.ofNat 64 cOff)
    (hpm : wsDword ws (pOff + 24) = B + BitVec.ofNat 64 mOff)
    (hpd : wsDword ws (pOff + 32) = B + BitVec.ofNat 64 dOff)
    (hmne : wsNat256 ws mOff ≠ 0) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS 0x802 rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws dOff (leBytes32 (Accel.arith256Mod
          (wsNat256 ws aOff) (wsNat256 ws bOff)
          (wsNat256 ws cOff) (wsNat256 ws mOff))))) := by
  intro R hR s hcr hPR hpcs
  subst hpcs
  have hfetch : s.code s.pc = some (.CSRS 0x802 rs1) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  rw [sepConj_assoc'] at hPR
  have hregs : s.getReg rs1 = rf.get rs1 :=
    holdsFor_regFileIs_getReg hPR hrs1
  have hMem := hPR
  rw [sepConj_left_comm] at hMem
  -- the parameter-block pointer and its five slots
  have hsrs1 : s.getReg rs1 = B + BitVec.ofNat 64 pOff := by rw [hregs, hp]
  have hslot : ∀ j : Nat, 8 ∣ j → j + 8 ≤ len →
      s.getMem (B + BitVec.ofNat 64 j) = wsDword ws j := fun j h8j hjfit =>
    holdsFor_bytesRegion_getMem hMem h8j (by omega)
  have haddr : ∀ j : Nat, s.getReg rs1 + BitVec.ofNat 64 j
      = B + BitVec.ofNat 64 (pOff + j) := fun j => by
    rw [hsrs1, add_ofNat_add]
  have hgA : s.getMem (s.getReg rs1) = B + BitVec.ofNat 64 aOff := by
    rw [hsrs1, hslot pOff h8p (by omega), hpa]
  have hgB : s.getMem (s.getReg rs1 + 8) = B + BitVec.ofNat 64 bOff := by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, haddr 8,
      hslot (pOff + 8) (by omega) (by omega), hpb]
  have hgC : s.getMem (s.getReg rs1 + 16) = B + BitVec.ofNat 64 cOff := by
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, haddr 16,
      hslot (pOff + 16) (by omega) (by omega), hpc]
  have hgM : s.getMem (s.getReg rs1 + 24) = B + BitVec.ofNat 64 mOff := by
    rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, haddr 24,
      hslot (pOff + 24) (by omega) (by omega), hpm]
  have hgD : s.getMem (s.getReg rs1 + 32) = B + BitVec.ofNat 64 dOff := by
    rw [show (32 : Word) = BitVec.ofNat 64 32 from rfl, haddr 32,
      hslot (pOff + 32) (by omega) (by omega), hpd]
  -- operand decodes
  have hrdA : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1)) 4)
      = wsNat256 ws aOff := by
    rw [hgA]; exact holdsFor_bytesRegion_readNat256 hMem h8a (by omega)
  have hrdB : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 8)) 4)
      = wsNat256 ws bOff := by
    rw [hgB]; exact holdsFor_bytesRegion_readNat256 hMem h8b (by omega)
  have hrdC : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 16)) 4)
      = wsNat256 ws cOff := by
    rw [hgC]; exact holdsFor_bytesRegion_readNat256 hMem h8c (by omega)
  have hrdM : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 24)) 4)
      = wsNat256 ws mOff := by
    rw [hgM]; exact holdsFor_bytesRegion_readNat256 hMem h8m (by omega)
  -- validity
  have hvrange : ∀ (k n : Nat), 8 ∣ k → k + 8 * n ≤ len →
      MachineState.validDwordRange (B + BitVec.ofNat 64 k) n = true :=
    fun k n h8k hkfit => validDwordRange_of_window hb8 hvalid h8k hkfit
  have hvmod : (!(Accel.leLimbsToNat
      (s.readWords (s.getMem (s.getReg rs1 + 24)) 4) == 0)) = true := by
    rw [hrdM]
    simpa using hmne
  have hvalidCsrs : s.csrsValid 0x802 rs1 = true := by
    rw [csrsValid_arith256]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hvmod⟩
    · rw [hsrs1]; exact hvrange pOff 5 h8p (by omega)
    · rw [hgA]; exact hvrange aOff 4 h8a (by omega)
    · rw [hgB]; exact hvrange bOff 4 h8b (by omega)
    · rw [hgC]; exact hvrange cOff 4 h8c (by omega)
    · rw [hgM]; exact hvrange mOff 4 h8m (by omega)
    · rw [hgD]; exact hvrange dOff 4 h8d (by omega)
  -- the step
  have hstep : step s = some (execInstrBr s (.CSRS 0x802 rs1)) :=
    step_csrs hfetch hvalidCsrs
  -- the memory effect: one writeWords at the output pointer
  have hwrite : s.execCsrs 0x802 rs1
      = s.writeWords (B + BitVec.ofNat 64 dOff)
          (Accel.natToLeLimbs 4 (Accel.arith256Mod
            (wsNat256 ws aOff) (wsNat256 ws bOff)
            (wsNat256 ws cOff) (wsNat256 ws mOff))) := by
    show s.writeWords (s.csrsWrite 0x802 rs1).1 (s.csrsWrite 0x802 rs1).2 = _
    rw [csrsWrite_arith256, hgD, hrdA, hrdB, hrdC, hrdM]
  -- assemble the post-state
  have hW := holdsFor_bytesRegion_writeWords
    (Accel.natToLeLimbs 4 (Accel.arith256Mod
      (wsNat256 ws aOff) (wsNat256 ws bOff)
      (wsNat256 ws cOff) (wsNat256 ws mOff)))
    ws s dOff hMem h8d
    (by rw [length_natToLeLimbs]; omega)
  refine ⟨1, Nat.le_refl 1,
    ((s.execCsrs 0x802 rs1).setPC (s.pc + 4)), ?_, ?_, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep]
    rfl
  · rfl
  · have hpcf : ((bytesRegion B (setBytes ws dOff (leBytes32 (Accel.arith256Mod
        (wsNat256 ws aOff) (wsNat256 ws bOff)
        (wsNat256 ws cOff) (wsNat256 ws mOff)))))
        ** ((regFileIs rf) ** R)).pcFree :=
      pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (pcFree_regFileIs _) hR)
    have hfin := holdsFor_pcFree_setPC (v := s.pc + 4) hpcf hW
    rw [← hwrite] at hfin
    rw [sepConj_left_comm, ← sepConj_assoc'] at hfin
    exact hfin

-- ============================================================================
-- The wrapper routine: `csrs 0x802, rs1 ; jalr x0, ra, 0`
-- ============================================================================

/-- The two-instruction Arith256Mod wrapper body. -/
def arith256ModProgram (rs1 : Reg) : Program :=
  [.CSRS 0x802 rs1, .JALR .x0 .x1 0]

/-- The wrapper triple in the C-ABI calling shape (`FnHandleS.sound`'s
    core): enter at `entry` with an aligned return address in `ra`, come
    back to it in 2 steps with the output buffer rewritten and everything
    else — registers, the rest of the window, the ambient `A` — intact. -/
theorem csrs_arith256Mod_ret_spec
    (entry : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff aOff bOff cOff mOff dOff : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 40 ≤ len)
    (h8a : 8 ∣ aOff) (hafit : aOff + 32 ≤ len)
    (h8b : 8 ∣ bOff) (hbfit : bOff + 32 ≤ len)
    (h8c : 8 ∣ cOff) (hcfit : cOff + 32 ≤ len)
    (h8m : 8 ∣ mOff) (hmfit : mOff + 32 ≤ len)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 32 ≤ len)
    (hpa : wsDword ws pOff = B + BitVec.ofNat 64 aOff)
    (hpb : wsDword ws (pOff + 8) = B + BitVec.ofNat 64 bOff)
    (hpc : wsDword ws (pOff + 16) = B + BitVec.ofNat 64 cOff)
    (hpm : wsDword ws (pOff + 24) = B + BitVec.ofNat 64 mOff)
    (hpd : wsDword ws (pOff + 32) = B + BitVec.ofNat 64 dOff)
    (hmne : wsNat256 ws mOff ≠ 0)
    (A : Assertion) (hA : A.pcFree)
    (ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 2 entry ret
      (CodeReq.ofProg entry (arith256ModProgram rs1))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B ws) ** A))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B
        (setBytes ws dOff (leBytes32 (Accel.arith256Mod
          (wsNat256 ws aOff) (wsNat256 ws bOff)
          (wsNat256 ws cOff) (wsNat256 ws mOff))))) ** A)) := by
  -- the CSRS step, framed with the ambient A and the return address
  have h1 := cpsTripleWithin_frameL (.x1 ↦ᵣ ret) (by pcFree)
    (cpsTripleWithin_frameR A hA
      (csrs_arith256Mod_spec_within entry rs1 hrs1 B len ws rf hwslen hb8
        hvalid pOff aOff bOff cOff mOff dOff hp h8p hpfit h8a hafit h8b hbfit
        h8c hcfit h8m hmfit h8d hdfit hpa hpb hpc hpm hpd hmne))
  have h1' := cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg entry (arith256ModProgram rs1))
    (fun a i h => ofProg_head a i h) h1
  -- the return epilogue
  have h2 := Fn.jalr_ret_spec (entry + 4) ret halign
    (P := ((regFileIs rf) ** bytesRegion B
      (setBytes ws dOff (leBytes32 (Accel.arith256Mod
        (wsNat256 ws aOff) (wsNat256 ws bOff)
        (wsNat256 ws cOff) (wsNat256 ws mOff))))) ** A)
    (pcFree_sepConj
      (pcFree_sepConj (pcFree_regFileIs _) (bytesRegion_pcFree _ _)) hA)
  have h2' := cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg entry (arith256ModProgram rs1))
    (fun a i h => ofProg_cons_tail (by simp)
      a i (by rwa [CodeReq.ofProg_singleton])) h2
  exact cpsTripleWithin_seq_same_cr h1' h2'

-- ============================================================================
-- The canonical accelerator handle
-- ============================================================================

/-- Call-site obligation of the Arith256Mod wrapper: `rs1` holds the
    parameter-block pointer, the block's five pointers land at the given
    window offsets, and the decoded modulus is nonzero.  The offsets'
    static side conditions (alignment, fit) live in the handle
    constructor, not here. -/
def arith256ModPre (B : Word) (rs1 : Reg)
    (pOff aOff bOff cOff mOff dOff : Nat) : Reach :=
  fun rf ws _ =>
    rf.get rs1 = B + BitVec.ofNat 64 pOff
    ∧ wsDword ws pOff = B + BitVec.ofNat 64 aOff
    ∧ wsDword ws (pOff + 8) = B + BitVec.ofNat 64 bOff
    ∧ wsDword ws (pOff + 16) = B + BitVec.ofNat 64 cOff
    ∧ wsDword ws (pOff + 24) = B + BitVec.ofNat 64 mOff
    ∧ wsDword ws (pOff + 32) = B + BitVec.ofNat 64 dOff
    ∧ wsNat256 ws mOff ≠ 0

/-- Snapshot-parameterized guarantee of the Arith256Mod wrapper: the
    output buffer becomes `(a·b + c) mod m` over the *entry* window's
    decoded operands; registers and the ambient assertion are untouched. -/
def arith256ModPost (aOff bOff cOff mOff dOff : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf = rf₀ ∧ A = A₀
    ∧ ws = setBytes ws₀ dOff (leBytes32 (Accel.arith256Mod
        (wsNat256 ws₀ aOff) (wsNat256 ws₀ bOff)
        (wsNat256 ws₀ cOff) (wsNat256 ws₀ mOff)))

/-- The handle's calling contract, standalone (kept out of the structure
    literal so projecting the handle's other fields stays cheap). -/
theorem arith256ModHandle_sound (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff aOff bOff cOff mOff dOff : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 40 ≤ len)
    (h8a : 8 ∣ aOff) (hafit : aOff + 32 ≤ len)
    (h8b : 8 ∣ bOff) (hbfit : bOff + 32 ≤ len)
    (h8c : 8 ∣ cOff) (hcfit : cOff + 32 ≤ len)
    (h8m : 8 ∣ mOff) (hmfit : mOff + 32 ≤ len)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 32 ≤ len) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree →
      arith256ModPre B rs1 pOff aOff bOff cOff mOff dOff rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (arith256ModProgram rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (arith256ModPost aOff bOff cOff mOff dOff rf₀ ws₀ A₀)) := by
    intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
    obtain ⟨hp, hpa, hpb, hpc, hpm, hpd, hmne⟩ := hpre
    have hcore := csrs_arith256Mod_ret_spec entry rs1 hrs1 B len ws₀ rf₀
      hlen hrw.1 hrw.2.2 pOff aOff bOff cOff mOff dOff hp h8p hpfit
      h8a hafit h8b hbfit h8c hcfit h8m hmfit h8d hdfit
      hpa hpb hpc hpm hpd hmne
      (A₀ ** bytesRegion ro.base ro.bytes)
      (pcFree_sepConj hApc (bytesRegion_pcFree _ _)) ret halign
    refine cpsTripleWithin_weaken (fun hq hh => ?_) (fun hq hh => ?_) hcore
    · -- pre: unfold the one-point asrtM into the concrete sep-conj
      rw [show asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀)
          = (asrtOf ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀)
            ** bytesRegion ro.base ro.bytes) from rfl,
        sepConj_comm'] at hh
      rw [sepConj_comm']
      refine sepConj_mono_left (fun hq' hh' => ?_) hq hh
      rw [← sepConj_assoc']
      refine sepConj_mono_left (fun hq'' hh'' => ?_) hq' hh'
      obtain ⟨rf, ws', A, -, -, ⟨rfl, rfl, rfl⟩, hsts⟩ := hh''
      exact hsts
    · -- post: repackage the concrete sep-conj as asrtM of the post family
      rw [show asrtM ro ⟨B, len⟩
            (arith256ModPost aOff bOff cOff mOff dOff rf₀ ws₀ A₀)
          = (asrtOf ⟨B, len⟩
              (arith256ModPost aOff bOff cOff mOff dOff rf₀ ws₀ A₀)
            ** bytesRegion ro.base ro.bytes) from rfl,
        sepConj_comm']
      rw [sepConj_comm'] at hh
      refine sepConj_mono_left (fun hq' hh' => ?_) hq hh
      rw [← sepConj_assoc'] at hh'
      refine sepConj_mono_left (fun hq'' hh'' => ?_) hq' hh'
      exact ⟨rf₀, _, A₀, by rw [length_setBytes]; exact hlen, hApc,
        ⟨rfl, rfl, rfl⟩, hh''⟩

/-- **The canonical accelerator-seam handle** (bead 4ch8f.11): the
    Arith256Mod wrapper packaged as a snapshot-parameterized callee.
    Consumed by SAsm kernels via `Stmt.callRegS`; its `sound` field is
    the hand-proven machine triple `csrs_arith256Mod_ret_spec` — no SAsm
    block engine involvement.  `ro` is the caller's read-only region
    (framed; the wrapper never touches it). -/
def arith256ModHandle (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff aOff bOff cOff mOff dOff : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 40 ≤ len)
    (h8a : 8 ∣ aOff) (hafit : aOff + 32 ≤ len)
    (h8b : 8 ∣ bOff) (hbfit : bOff + 32 ≤ len)
    (h8c : 8 ∣ cOff) (hcfit : cOff + 32 ≤ len)
    (h8m : 8 ∣ mOff) (hmfit : mOff + 32 ≤ len)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 32 ≤ len) : FnHandleS where
  entry := entry
  code := CodeReq.ofProg entry (arith256ModProgram rs1)
  nSteps := 2
  region := ro
  rw := ⟨B, len⟩
  pre := arith256ModPre B rs1 pOff aOff bOff cOff mOff dOff
  post := arith256ModPost aOff bOff cOff mOff dOff
  sound := arith256ModHandle_sound entry rs1 hrs1 ro B len hrw
    pOff aOff bOff cOff mOff dOff h8p hpfit h8a hafit h8b hbfit
    h8c hcfit h8m hmfit h8d hdfit

end SAsm
end EvmAsm.Rv64
