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
    (little-endian, matching `Accel.leLimbsToNat`/`Accel.natToLeLimbs`);
    `wsNat` / `leBytesN` / `wsPair` / `pairBytes`: their `nLimbs`-generic
    forms (bead 4ch8f.11.6).
  - Window-locality lemmas (`wsDword_setBytes_low/high`,
    `wsNat_setBytes_low/high`, `wsNat_setBytes_leBytesN`,
    `wsPair_setBytes_pairBytes`, …): promoted from the pilot
    (`PowLadderDemo`) so every kernel gets them for free.
  - `holdsFor_bytesRegion_readWords`: `MachineState.readWords` over a
    framed window reads the packed window dwords.
  - `holdsFor_bytesRegion_writeWords`: `MachineState.writeWords` into a
    framed window splices the payload bytes (the `execCsrs` update, at
    separation-logic granularity).
  - `csrs_arith256Mod_spec_within`: the one-step triple for
    `csrs 0x802, rs1` — output buffer := `(a·b + c) mod m` over the
    window-decoded operands (the pilot's 4-limb instance).
  - `csrs_arith256Mod_ret_spec`: the triple with the `jalr x0, ra, 0`
    return epilogue, in exactly the `FnHandleS.sound` calling shape.
  - **The generalized seam contract** (bead 4ch8f.11.6): the generic
    one-step skeleton (`csrs_step_spec_within`), return-epilogue
    composition (`csrs_ret_spec_of_step`) and `FnHandleS` packaging
    (`csrs_handleS_sound`), instantiated at every crypto accelerator id:
    * `arithModHandle`  — `nLimbs`-parametric Arith256Mod/Arith384Mod
      (`ArithWidth`: `0x802` 4 limbs, `0x80B` 6 limbs);
    * `curveAddHandle` / `curveDblHandle` — the affine curve ops
      (`CurveId`: secp256k1 `0x803/0x804`, BN254 `0x806/0x807`,
      BLS12-381 `0x80C/0x80D`) with `ptValid`-style preconditions
      (reduced coordinates, `x₁ ≠ x₂` resp. `y ≠ 0`);
    * `cxHandle` — the Fp2 "complex" ops (`Fp2Id`/`CxOp`: BN254
      `0x808/0x809/0x80A`, BLS12-381 `0x80E/0x80F/0x810`, `u² = −1`)
      with reduced-component preconditions.
    Every handle's postcondition is decode-valued: the output buffer
    becomes the corresponding `Accel.*` Nat-modular function of the
    *entry* window's decoded operands, so aliasing needs no side
    conditions (the pilot's load-bearing discovery).
  - **The Sha256f handle** (bead 4ch8f.18.1): `wsDwords` (the dword-LIST
    window view for u32-packed operands, with `_setBytes_low/high` and
    write-back-decode locality lemmas), `csrs_sha256Compress_spec_within`
    / `csrs_sha256Compress_ret_spec` / `sha256CompressHandle` — CSR
    `0x805`, param block `[state*, input*]`, state := the real
    `Accel.sha256Compress` of the entry window's decoded state/block
    (`sha256Dwords`/`sha256Bytes`).  Unblocks the `zkvm_sha256` port
    (bead 4ch8f.18).
-/

import EvmAsm.Rv64.ZiskAccel
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Crypto.PowLadder

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

-- ============================================================================
-- nLimbs-generic window decode / encode (bead 4ch8f.11.6)
-- ============================================================================

/-- The `8*nl`-byte little-endian natural at byte offset `k` of a window
    (`nl` LE u64 limbs — what the accelerators consume through
    `Accel.leLimbsToNat ∘ MachineState.readWords`).  `wsNat 4 = wsNat256`
    (`wsNat_four`); `wsNat 6` is the Arith384Mod/BLS12-381 view. -/
def wsNat (nl : Nat) (ws : List (BitVec 8)) (k : Nat) : Nat :=
  Accel.leLimbsToNat ((List.range nl).map fun i => wsDword ws (k + 8 * i))

theorem wsNat_four (ws : List (BitVec 8)) (k : Nat) :
    wsNat 4 ws k = wsNat256 ws k := by
  unfold wsNat wsNat256
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  norm_num

/-- The `8*nl`-byte little-endian image of (the low `64*nl` bits of) a
    natural — the byte-level view of `Accel.natToLeLimbs nl`. -/
def leBytesN (nl v : Nat) : List (BitVec 8) :=
  (Accel.natToLeLimbs nl v).flatMap dwordBytes

theorem leBytes32_eq (v : Nat) : leBytes32 v = leBytesN 4 v := rfl

theorem length_flatMap_dwordBytes (wsL : List Word) :
    (wsL.flatMap dwordBytes).length = 8 * wsL.length := by
  induction wsL with
  | nil => rfl
  | cons w rest ih =>
      simp only [List.flatMap_cons, List.length_append, length_dwordBytes,
        List.length_cons, ih]
      omega

@[simp] theorem length_leBytesN (nl v : Nat) : (leBytesN nl v).length = 8 * nl := by
  rw [leBytesN, length_flatMap_dwordBytes, length_natToLeLimbs]

/-- An affine point / Fp2 element decoded from the window: `x` (resp. the
    real component) at `k`, `y` (resp. the imaginary component) at
    `k + 8*nl` — the accelerator wire format. -/
def wsPair (nl : Nat) (ws : List (BitVec 8)) (k : Nat) : Nat × Nat :=
  (wsNat nl ws k, wsNat nl ws (k + 8 * nl))

/-- The `16*nl`-byte wire image of a coordinate/component pair. -/
def pairBytes (nl : Nat) (v : Nat × Nat) : List (BitVec 8) :=
  leBytesN nl v.1 ++ leBytesN nl v.2

@[simp] theorem length_pairBytes (nl : Nat) (v : Nat × Nat) :
    (pairBytes nl v).length = 16 * nl := by
  rw [pairBytes, List.length_append, length_leBytesN, length_leBytesN]
  omega

/-- Concatenated limb payloads flatten to the pair's wire image (the
    `curveAddL`/`curveDblL`/`complex*L` output shape). -/
theorem flatMap_pairLimbs (nl a b : Nat) :
    (Accel.natToLeLimbs nl a ++ Accel.natToLeLimbs nl b).flatMap dwordBytes
      = pairBytes nl (a, b) := by
  rw [List.flatMap_append]
  rfl

/-- Decode an `nl`-limb operand through `readWords`, as the window natural. -/
theorem holdsFor_bytesRegion_readNat {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {nl k : Nat} (h8 : 8 ∣ k) (hfit : k + 8 * nl ≤ bs.length) :
    Accel.leLimbsToNat (s.readWords (b + BitVec.ofNat 64 k) nl) = wsNat nl bs k := by
  rw [holdsFor_bytesRegion_readWords hPR nl k h8 hfit]
  rfl

/-- Decode the first half of a `2*nl`-limb operand read (the `x`
    coordinate / real component of a wire pair). -/
theorem holdsFor_bytesRegion_readPair_fst {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {nl k : Nat} (h8 : 8 ∣ k) (hfit : k + 16 * nl ≤ bs.length) :
    Accel.leLimbsToNat ((s.readWords (b + BitVec.ofNat 64 k) (2 * nl)).take nl)
      = wsNat nl bs k := by
  rw [holdsFor_bytesRegion_readWords hPR (2 * nl) k h8 (by omega),
    ← List.map_take, show 2 * nl = nl + nl from by omega, List.range_add,
    List.take_left' (by simp)]
  rfl

/-- Decode the second half of a `2*nl`-limb operand read (the `y`
    coordinate / imaginary component of a wire pair). -/
theorem holdsFor_bytesRegion_readPair_snd {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {nl k : Nat} (h8 : 8 ∣ k) (hfit : k + 16 * nl ≤ bs.length) :
    Accel.leLimbsToNat ((s.readWords (b + BitVec.ofNat 64 k) (2 * nl)).drop nl)
      = wsNat nl bs (k + 8 * nl) := by
  rw [holdsFor_bytesRegion_readWords hPR (2 * nl) k h8 (by omega),
    ← List.map_drop, show 2 * nl = nl + nl from by omega, List.range_add,
    List.drop_left' (by simp), List.map_map]
  unfold wsNat
  congr 1
  apply List.map_congr_left
  intro i _
  show wsDword bs (k + 8 * (nl + i)) = wsDword bs (k + 8 * nl + 8 * i)
  congr 1
  omega

-- ============================================================================
-- Window-locality lemmas (promoted from the pilot, bead 4ch8f.11.6)
-- ============================================================================

/-- Reading a dword strictly below a splice is unchanged. -/
theorem wsDword_setBytes_low {bs ns : List (BitVec 8)} {j k : Nat}
    (h : k + 8 ≤ j) :
    wsDword (setBytes bs j ns) k = wsDword bs k := by
  unfold wsDword
  have htake : (setBytes bs j ns).take j = bs.take j :=
    setBytes_take_of_ge ns bs j j (Nat.le_refl j)
  have h1 : (((setBytes bs j ns).take j).drop k).take 8
      = ((bs.take j).drop k).take 8 := by rw [htake]
  rw [List.drop_take, List.drop_take, List.take_take, List.take_take,
    Nat.min_eq_left (by omega)] at h1
  rw [h1]

/-- Reading a dword entirely above a splice is unchanged. -/
theorem wsDword_setBytes_high {bs ns : List (BitVec 8)} {j k : Nat}
    (h : j + ns.length ≤ k) :
    wsDword (setBytes bs j ns) k = wsDword bs k := by
  unfold wsDword
  rw [setBytes_drop_of_le ns bs j k h]

/-- Reading an `nl`-limb operand strictly below a splice is unchanged. -/
theorem wsNat_setBytes_low {nl : Nat} {bs ns : List (BitVec 8)} {j k : Nat}
    (h : k + 8 * nl ≤ j) :
    wsNat nl (setBytes bs j ns) k = wsNat nl bs k := by
  unfold wsNat
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact wsDword_setBytes_low (by omega)

/-- Reading an `nl`-limb operand entirely above a splice is unchanged. -/
theorem wsNat_setBytes_high {nl : Nat} {bs ns : List (BitVec 8)} {j k : Nat}
    (h : j + ns.length ≤ k) :
    wsNat nl (setBytes bs j ns) k = wsNat nl bs k := by
  unfold wsNat
  congr 1
  apply List.map_congr_left
  intro i hi
  exact wsDword_setBytes_high (by omega)

/-- Reading a 256-bit operand strictly below a splice is unchanged. -/
theorem wsNat256_setBytes_low {bs ns : List (BitVec 8)} {j k : Nat}
    (h : k + 32 ≤ j) :
    wsNat256 (setBytes bs j ns) k = wsNat256 bs k := by
  rw [← wsNat_four, ← wsNat_four]
  exact wsNat_setBytes_low (by omega)

/-- Slicing dword `t` back out of a limb list's byte image. -/
theorem flatMap_dwordBytes_slice :
    ∀ (wsL : List Word) (t : Nat), t < wsL.length →
      ((wsL.flatMap dwordBytes).drop (8 * t)).take 8 = dwordBytes (wsL.getD t 0)
  | [], t, ht => absurd ht (by simp)
  | w :: rest, 0, _ => by
      simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getD_cons_zero]
      rw [List.take_append_of_le_length (by rw [length_dwordBytes])]
      exact List.take_of_length_le (by rw [length_dwordBytes])
  | w :: rest, t + 1, ht => by
      simp only [List.flatMap_cons, List.getD_cons_succ]
      rw [show 8 * (t + 1) = (dwordBytes w).length + (8 * t) from by
          rw [length_dwordBytes]; omega,
        ← List.drop_drop, List.drop_left]
      exact flatMap_dwordBytes_slice rest t (by simpa using ht)

/-- Reading a list back out by position. -/
private theorem map_getD_range {α : Type _} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ List.cons rfl ?_
      rw [show ((fun i => (x :: xs).getD i d) ∘ Nat.succ)
          = (fun i => xs.getD i d) from funext fun i => List.getD_cons_succ]
      exact ih

/-- Decoding the freshly written output buffer recovers the value. -/
theorem wsNat_setBytes_leBytesN {nl : Nat} {bs : List (BitVec 8)} {j v : Nat}
    (hv : v < 2 ^ (64 * nl)) (hfit : j + 8 * nl ≤ bs.length) :
    wsNat nl (setBytes bs j (leBytesN nl v)) j = v := by
  have hslot : ((setBytes bs j (leBytesN nl v)).drop j).take (8 * nl)
      = leBytesN nl v := by
    have := setBytes_slot bs (leBytesN nl v) j
      (by rw [length_leBytesN]; omega)
    rwa [length_leBytesN] at this
  -- per-limb: the dword at j + 8t is limb t of the payload
  have hlimb : ∀ t : Nat, t < nl →
      wsDword (setBytes bs j (leBytesN nl v)) (j + 8 * t)
        = (Accel.natToLeLimbs nl v).getD t 0 := by
    intro t ht
    unfold wsDword
    have hs8 : (((setBytes bs j (leBytesN nl v)).drop j).drop (8 * t)).take 8
        = ((leBytesN nl v).drop (8 * t)).take 8 := by
      conv_rhs => rw [← hslot]
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
    rw [show j + 8 * t = j + (8 * t) from rfl, ← List.drop_drop, hs8,
      show leBytesN nl v = (Accel.natToLeLimbs nl v).flatMap dwordBytes from rfl,
      flatMap_dwordBytes_slice (Accel.natToLeLimbs nl v) t (by simpa using ht),
      packBytes_dwordBytes]
  unfold wsNat
  rw [List.map_congr_left (fun i hi => hlimb i (List.mem_range.mp hi))]
  rw [show (List.range nl).map (fun i => (Accel.natToLeLimbs nl v).getD i 0)
      = Accel.natToLeLimbs nl v from by
    have h := map_getD_range (Accel.natToLeLimbs nl v) 0
    rwa [length_natToLeLimbs] at h]
  exact Crypto.leLimbsToNat_natToLeLimbs nl v hv

/-- Decoding the freshly written output buffer recovers the value
    (pilot instance). -/
theorem wsNat256_setBytes_leBytes32 {bs : List (BitVec 8)} {j v : Nat}
    (hv : v < 2 ^ 256) (hfit : j + 32 ≤ bs.length) :
    wsNat256 (setBytes bs j (leBytes32 v)) j = v := by
  rw [← wsNat_four, leBytes32_eq]
  exact wsNat_setBytes_leBytesN hv (by omega)

/-- Decoding the freshly written pair output recovers both halves
    (the curve/complex handles' output shape). -/
theorem wsPair_setBytes_pairBytes {nl : Nat} {bs : List (BitVec 8)}
    {j : Nat} {v : Nat × Nat}
    (hv1 : v.1 < 2 ^ (64 * nl)) (hv2 : v.2 < 2 ^ (64 * nl))
    (hfit : j + 16 * nl ≤ bs.length) :
    wsPair nl (setBytes bs j (pairBytes nl v)) j = v := by
  have hsplit : setBytes bs j (pairBytes nl v)
      = setBytes (setBytes bs j (leBytesN nl v.1)) (j + 8 * nl)
          (leBytesN nl v.2) := by
    rw [pairBytes, setBytes_append, length_leBytesN]
  unfold wsPair
  rw [hsplit]
  refine Prod.ext ?_ ?_
  · show wsNat nl _ j = v.1
    rw [wsNat_setBytes_low (Nat.le_refl _)]
    exact wsNat_setBytes_leBytesN hv1 (by omega)
  · show wsNat nl _ (j + 8 * nl) = v.2
    exact wsNat_setBytes_leBytesN hv2
      (by rw [length_setBytes]; omega)

-- ============================================================================
-- The generic accelerator-step skeleton (bead 4ch8f.11.6)
-- ============================================================================

/-- Any modeled accelerator step whose semantic facts — `csrsValid` and
    the `csrsWrite` target/payload — have been discharged against the
    framed window: the payload's bytes are spliced in at `dOff` and
    nothing else moves, not even a register.  Every per-id `*_spec_within`
    below is this skeleton plus decode reasoning. -/
theorem csrs_step_spec_within (csr : BitVec 12) (rs1 : Reg)
    (base : Word) (B : Word) (ws : List (BitVec 8)) (rf : RegFile)
    (dOff : Nat) (payload : List Word)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 8 * payload.length ≤ ws.length)
    (hsem : ∀ (R : Assertion) (s : MachineState),
      (((regFileIs rf) ** bytesRegion B ws) ** R).holdsFor s →
      s.csrsValid csr rs1 = true ∧
      s.csrsWrite csr rs1 = (B + BitVec.ofNat 64 dOff, payload)) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS csr rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws dOff (payload.flatMap dwordBytes))) := by
  intro R hR s hcr hPR hpcs
  subst hpcs
  have hfetch : s.code s.pc = some (.CSRS csr rs1) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  obtain ⟨hvalidCsrs, hwriteCsrs⟩ := hsem R s hPR
  rw [sepConj_assoc'] at hPR
  have hMem := hPR
  rw [sepConj_left_comm] at hMem
  have hstep : step s = some (execInstrBr s (.CSRS csr rs1)) :=
    step_csrs hfetch hvalidCsrs
  have hwrite : s.execCsrs csr rs1
      = s.writeWords (B + BitVec.ofNat 64 dOff) payload := by
    show s.writeWords (s.csrsWrite csr rs1).1 (s.csrsWrite csr rs1).2 = _
    rw [hwriteCsrs]
  have hW := holdsFor_bytesRegion_writeWords payload ws s dOff hMem h8d hdfit
  refine ⟨1, Nat.le_refl 1,
    ((s.execCsrs csr rs1).setPC (s.pc + 4)), ?_, ?_, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep]
    rfl
  · rfl
  · have hpcf : ((bytesRegion B (setBytes ws dOff (payload.flatMap dwordBytes)))
        ** ((regFileIs rf) ** R)).pcFree :=
      pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (pcFree_regFileIs _) hR)
    have hfin := holdsFor_pcFree_setPC (v := s.pc + 4) hpcf hW
    rw [← hwrite] at hfin
    rw [sepConj_left_comm, ← sepConj_assoc'] at hfin
    exact hfin

/-- The canonical two-instruction accelerator wrapper body. -/
def csrsRetProgram (csr : BitVec 12) (rs1 : Reg) : Program :=
  [.CSRS csr rs1, .JALR .x0 .x1 0]

/-- Compose a one-step accelerator triple with the `jalr x0, ra, 0`
    return epilogue, in exactly the `FnHandleS.sound` calling shape. -/
theorem csrs_ret_spec_of_step {csr : BitVec 12} {rs1 : Reg} {entry : Word}
    {B : Word} {ws ws' : List (BitVec 8)} {rf : RegFile}
    (hstep : cpsTripleWithin 1 entry (entry + 4)
      (CodeReq.singleton entry (.CSRS csr rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B ws'))
    (A : Assertion) (hA : A.pcFree)
    (ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 2 entry ret (CodeReq.ofProg entry (csrsRetProgram csr rs1))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B ws) ** A))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B ws') ** A)) := by
  have h1 := cpsTripleWithin_frameL (.x1 ↦ᵣ ret) (by pcFree)
    (cpsTripleWithin_frameR A hA hstep)
  have h1' := cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg entry (csrsRetProgram csr rs1))
    (fun a i h => ofProg_head a i h) h1
  have h2 := Fn.jalr_ret_spec (entry + 4) ret halign
    (P := ((regFileIs rf) ** bytesRegion B ws') ** A)
    (pcFree_sepConj
      (pcFree_sepConj (pcFree_regFileIs _) (bytesRegion_pcFree _ _)) hA)
  have h2' := cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg entry (csrsRetProgram csr rs1))
    (fun a i h => ofProg_cons_tail (by simp)
      a i (by rwa [CodeReq.ofProg_singleton])) h2
  exact cpsTripleWithin_seq_same_cr h1' h2'

/-- Package a per-entry-state accelerator step triple as the
    `FnHandleS.sound` contract: precondition `pre`, snapshot-parameterized
    postcondition "the window becomes `img` of the entry window,
    registers and ambient assertion untouched". -/
theorem csrs_handleS_sound (entry : Word) (csr : BitVec 12) (rs1 : Reg)
    (ro : Region) (B : Word) (len : Nat)
    (pre : Reach) (img : List (BitVec 8) → List (BitVec 8))
    (himglen : ∀ ws : List (BitVec 8), ws.length = len → (img ws).length = len)
    (hstep : ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)),
      ws₀.length = len → (∃ A₀, pre rf₀ ws₀ A₀) →
      cpsTripleWithin 1 entry (entry + 4)
        (CodeReq.singleton entry (.CSRS csr rs1))
        ((regFileIs rf₀) ** bytesRegion B ws₀)
        ((regFileIs rf₀) ** bytesRegion B (img ws₀))) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree → pre rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (csrsRetProgram csr rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (fun rf ws A => rf = rf₀ ∧ A = A₀ ∧ ws = img ws₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  have hcore := csrs_ret_spec_of_step (hstep rf₀ ws₀ hlen ⟨A₀, hpre⟩)
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
          (fun rf ws A => rf = rf₀ ∧ A = A₀ ∧ ws = img ws₀)
        = (asrtOf ⟨B, len⟩
            (fun rf ws A => rf = rf₀ ∧ A = A₀ ∧ ws = img ws₀)
          ** bytesRegion ro.base ro.bytes) from rfl,
      sepConj_comm']
    rw [sepConj_comm'] at hh
    refine sepConj_mono_left (fun hq' hh' => ?_) hq hh
    rw [← sepConj_assoc'] at hh'
    refine sepConj_mono_left (fun hq'' hh'' => ?_) hq' hh'
    exact ⟨rf₀, _, A₀, himglen ws₀ hlen, hApc, ⟨rfl, rfl, rfl⟩, hh''⟩

-- ============================================================================
-- The accelerator id tables (bead 4ch8f.11.6)
-- ============================================================================

/-- The two modular-multiply-accumulate widths (`csrsWrite` routes both
    ids through the same `Accel.arith256Mod`). -/
inductive ArithWidth where
  | w256
  | w384
  deriving Repr, DecidableEq

namespace ArithWidth

/-- Limb count of the width. -/
def nl : ArithWidth → Nat
  | .w256 => 4
  | .w384 => 6

/-- CSR id of the width. -/
def csr : ArithWidth → BitVec 12
  | .w256 => 0x802
  | .w384 => 0x80B

end ArithWidth

/-- The three accelerator curves (all `y² = x³ + b` with `a = 0`;
    `p`/`nl` per `EvmAsm.Rv64.ZiskAccel`). -/
inductive CurveId where
  | secp256k1
  | bn254
  | bls12_381
  deriving Repr, DecidableEq

namespace CurveId

/-- Base-field modulus. -/
def p : CurveId → Nat
  | .secp256k1 => Accel.secpP
  | .bn254 => Accel.bn254P
  | .bls12_381 => Accel.bls12P

/-- Limbs per coordinate. -/
def nl : CurveId → Nat
  | .secp256k1 => 4
  | .bn254 => 4
  | .bls12_381 => 6

/-- CSR id of the chord addition. -/
def addCsr : CurveId → BitVec 12
  | .secp256k1 => 0x803
  | .bn254 => 0x806
  | .bls12_381 => 0x80C

/-- CSR id of the tangent doubling. -/
def dblCsr : CurveId → BitVec 12
  | .secp256k1 => 0x804
  | .bn254 => 0x807
  | .bls12_381 => 0x80D

end CurveId

/-- The two Fp2 ("complex", `u² = −1`) accelerator families. -/
inductive Fp2Id where
  | bn254
  | bls12_381
  deriving Repr, DecidableEq

/-- The three Fp2 operations. -/
inductive CxOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

namespace Fp2Id

/-- Base-field modulus. -/
def p : Fp2Id → Nat
  | .bn254 => Accel.bn254P
  | .bls12_381 => Accel.bls12P

/-- Limbs per component. -/
def nl : Fp2Id → Nat
  | .bn254 => 4
  | .bls12_381 => 6

/-- CSR id of the operation. -/
def csr : Fp2Id → CxOp → BitVec 12
  | .bn254, .add => 0x808
  | .bn254, .sub => 0x809
  | .bn254, .mul => 0x80A
  | .bls12_381, .add => 0x80E
  | .bls12_381, .sub => 0x80F
  | .bls12_381, .mul => 0x810

end Fp2Id

/-- The Fp2 operation on decoded component pairs — the Nat-modular value
    the corresponding `Accel.complex*L` wire function computes
    (`cxOp_complexL` below pins the correspondence definitionally). -/
def CxOp.op : CxOp → Nat → Nat × Nat → Nat × Nat → Nat × Nat
  | .add, P, u, v => ((u.1 + v.1) % P, (u.2 + v.2) % P)
  | .sub, P, u, v => ((u.1 + P - v.1) % P, (u.2 + P - v.2) % P)
  | .mul, P, u, v =>
      ((u.1 * v.1 + P * P - u.2 * v.2) % P, (u.1 * v.2 + u.2 * v.1) % P)

/-- The wire-format Fp2 operation of an op. -/
def CxOp.opL : CxOp → Nat → Nat → List Word → List Word → List Word
  | .add => Accel.complexAddL
  | .sub => Accel.complexSubL
  | .mul => Accel.complexMulL

/-- `Accel.complex*L` decodes to `CxOp.op` on the component pairs
    (definitional). -/
theorem cxOp_complexL (o : CxOp) (P nl : Nat) (f1 f2 : List Word) :
    o.opL P nl f1 f2
      = Accel.natToLeLimbs nl (o.op P
          (Accel.leLimbsToNat (f1.take nl), Accel.leLimbsToNat (f1.drop nl))
          (Accel.leLimbsToNat (f2.take nl), Accel.leLimbsToNat (f2.drop nl))).1
        ++ Accel.natToLeLimbs nl (o.op P
          (Accel.leLimbsToNat (f1.take nl), Accel.leLimbsToNat (f1.drop nl))
          (Accel.leLimbsToNat (f2.take nl), Accel.leLimbsToNat (f2.drop nl))).2 := by
  cases o <;> rfl

/-- `Accel.curveAddL` decodes to `Accel.curveAdd` on the coordinates
    (definitional). -/
theorem curveAddL_decode (p nl : Nat) (pt1 pt2 : List Word) :
    Accel.curveAddL p nl pt1 pt2
      = Accel.natToLeLimbs nl (Accel.curveAdd p
          (Accel.leLimbsToNat (pt1.take nl)) (Accel.leLimbsToNat (pt1.drop nl))
          (Accel.leLimbsToNat (pt2.take nl)) (Accel.leLimbsToNat (pt2.drop nl))).1
        ++ Accel.natToLeLimbs nl (Accel.curveAdd p
          (Accel.leLimbsToNat (pt1.take nl)) (Accel.leLimbsToNat (pt1.drop nl))
          (Accel.leLimbsToNat (pt2.take nl)) (Accel.leLimbsToNat (pt2.drop nl))).2
    := rfl

/-- `Accel.curveDblL` decodes to `Accel.curveDbl` on the coordinates
    (definitional). -/
theorem curveDblL_decode (p nl : Nat) (pt : List Word) :
    Accel.curveDblL p nl pt
      = Accel.natToLeLimbs nl (Accel.curveDbl p
          (Accel.leLimbsToNat (pt.take nl)) (Accel.leLimbsToNat (pt.drop nl))).1
        ++ Accel.natToLeLimbs nl (Accel.curveDbl p
          (Accel.leLimbsToNat (pt.take nl)) (Accel.leLimbsToNat (pt.drop nl))).2
    := rfl

-- ============================================================================
-- The nLimbs-parametric Arith256Mod/Arith384Mod handle
-- ============================================================================

/-- The `csrsValid` arm of an `ArithWidth` id (definitional). -/
private theorem csrsValid_arithMod (w : ArithWidth) (s : MachineState)
    (rs1 : Reg) :
    s.csrsValid w.csr rs1
      = (MachineState.validDwordRange (s.getReg rs1) 5 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1)) w.nl &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 8)) w.nl &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 16)) w.nl &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 24)) w.nl &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 32)) w.nl &&
         !(Accel.leLimbsToNat
             (s.readWords (s.getMem (s.getReg rs1 + 24)) w.nl) == 0)) := by
  cases w <;> rfl

/-- The `csrsWrite` arm of an `ArithWidth` id (definitional). -/
private theorem csrsWrite_arithMod (w : ArithWidth) (s : MachineState)
    (rs1 : Reg) :
    s.csrsWrite w.csr rs1
      = (s.getMem (s.getReg rs1 + 32), Accel.natToLeLimbs w.nl (Accel.arith256Mod
          (Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1)) w.nl))
          (Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 8)) w.nl))
          (Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 16)) w.nl))
          (Accel.leLimbsToNat
            (s.readWords (s.getMem (s.getReg rs1 + 24)) w.nl)))) := by
  cases w <;> rfl

/-- The `nLimbs`-parametric Arith256Mod/Arith384Mod step: `csrs w.csr, rs1`
    with `rs1` pointing at a `[a*, b*, c*, module*, d*]` parameter block
    whose five pointers land inside the window at dword-aligned,
    `8*nl`-byte-fitting offsets; the output buffer becomes
    `(a·b + c) mod m` over the window-decoded operands.  Operand offsets
    may alias arbitrarily (decode-valued post). -/
theorem csrs_arithMod_spec_within (w : ArithWidth)
    (base : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff aOff bOff cOff mOff dOff : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 40 ≤ len)
    (h8a : 8 ∣ aOff) (hafit : aOff + 8 * w.nl ≤ len)
    (h8b : 8 ∣ bOff) (hbfit : bOff + 8 * w.nl ≤ len)
    (h8c : 8 ∣ cOff) (hcfit : cOff + 8 * w.nl ≤ len)
    (h8m : 8 ∣ mOff) (hmfit : mOff + 8 * w.nl ≤ len)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 8 * w.nl ≤ len)
    (hpa : wsDword ws pOff = B + BitVec.ofNat 64 aOff)
    (hpb : wsDword ws (pOff + 8) = B + BitVec.ofNat 64 bOff)
    (hpc : wsDword ws (pOff + 16) = B + BitVec.ofNat 64 cOff)
    (hpm : wsDword ws (pOff + 24) = B + BitVec.ofNat 64 mOff)
    (hpd : wsDword ws (pOff + 32) = B + BitVec.ofNat 64 dOff)
    (hmne : wsNat w.nl ws mOff ≠ 0) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS w.csr rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws dOff (leBytesN w.nl (Accel.arith256Mod
          (wsNat w.nl ws aOff) (wsNat w.nl ws bOff)
          (wsNat w.nl ws cOff) (wsNat w.nl ws mOff))))) := by
  refine csrs_step_spec_within w.csr rs1 base B ws rf dOff
    (Accel.natToLeLimbs w.nl (Accel.arith256Mod
      (wsNat w.nl ws aOff) (wsNat w.nl ws bOff)
      (wsNat w.nl ws cOff) (wsNat w.nl ws mOff)))
    h8d (by rw [length_natToLeLimbs]; omega) ?_
  intro R s hPR
  rw [sepConj_assoc'] at hPR
  have hregs : s.getReg rs1 = rf.get rs1 :=
    holdsFor_regFileIs_getReg hPR hrs1
  have hMem := hPR
  rw [sepConj_left_comm] at hMem
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
  have hrdA : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1)) w.nl)
      = wsNat w.nl ws aOff := by
    rw [hgA]; exact holdsFor_bytesRegion_readNat hMem h8a (by omega)
  have hrdB : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 8)) w.nl)
      = wsNat w.nl ws bOff := by
    rw [hgB]; exact holdsFor_bytesRegion_readNat hMem h8b (by omega)
  have hrdC : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 16)) w.nl)
      = wsNat w.nl ws cOff := by
    rw [hgC]; exact holdsFor_bytesRegion_readNat hMem h8c (by omega)
  have hrdM : Accel.leLimbsToNat (s.readWords (s.getMem (s.getReg rs1 + 24)) w.nl)
      = wsNat w.nl ws mOff := by
    rw [hgM]; exact holdsFor_bytesRegion_readNat hMem h8m (by omega)
  have hvrange : ∀ (k n : Nat), 8 ∣ k → k + 8 * n ≤ len →
      MachineState.validDwordRange (B + BitVec.ofNat 64 k) n = true :=
    fun k n h8k hkfit => validDwordRange_of_window hb8 hvalid h8k hkfit
  refine ⟨?_, ?_⟩
  · rw [csrsValid_arithMod w s rs1]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hsrs1]; exact hvrange pOff 5 h8p (by omega)
    · rw [hgA]; exact hvrange aOff w.nl h8a (by omega)
    · rw [hgB]; exact hvrange bOff w.nl h8b (by omega)
    · rw [hgC]; exact hvrange cOff w.nl h8c (by omega)
    · rw [hgM]; exact hvrange mOff w.nl h8m (by omega)
    · rw [hgD]; exact hvrange dOff w.nl h8d (by omega)
    · rw [hrdM]; simpa using hmne
  · rw [csrsWrite_arithMod w s rs1, hgD, hrdA, hrdB, hrdC, hrdM]

/-- Call-site obligation of the `nLimbs`-parametric Arith*Mod wrapper:
    `rs1` holds the parameter-block pointer, the block's five pointers
    land at the given window offsets, and the decoded modulus is nonzero.
    Exactly the accelerator's own `csrsValid` operand conditions — the
    static side conditions (alignment, fit) live in the handle
    constructor. -/
def arithModPre (w : ArithWidth) (B : Word) (rs1 : Reg)
    (pOff aOff bOff cOff mOff dOff : Nat) : Reach :=
  fun rf ws _ =>
    rf.get rs1 = B + BitVec.ofNat 64 pOff
    ∧ wsDword ws pOff = B + BitVec.ofNat 64 aOff
    ∧ wsDword ws (pOff + 8) = B + BitVec.ofNat 64 bOff
    ∧ wsDword ws (pOff + 16) = B + BitVec.ofNat 64 cOff
    ∧ wsDword ws (pOff + 24) = B + BitVec.ofNat 64 mOff
    ∧ wsDword ws (pOff + 32) = B + BitVec.ofNat 64 dOff
    ∧ wsNat w.nl ws mOff ≠ 0

/-- Snapshot-parameterized guarantee of the Arith*Mod wrapper: the output
    buffer becomes `(a·b + c) mod m` over the *entry* window's decoded
    operands; registers and the ambient assertion untouched. -/
def arithModPost (w : ArithWidth) (aOff bOff cOff mOff dOff : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf = rf₀ ∧ A = A₀
    ∧ ws = setBytes ws₀ dOff (leBytesN w.nl (Accel.arith256Mod
        (wsNat w.nl ws₀ aOff) (wsNat w.nl ws₀ bOff)
        (wsNat w.nl ws₀ cOff) (wsNat w.nl ws₀ mOff)))

/-- The Arith*Mod handle's calling contract, standalone. -/
theorem arithModHandle_sound (w : ArithWidth) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff aOff bOff cOff mOff dOff : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 40 ≤ len)
    (h8a : 8 ∣ aOff) (hafit : aOff + 8 * w.nl ≤ len)
    (h8b : 8 ∣ bOff) (hbfit : bOff + 8 * w.nl ≤ len)
    (h8c : 8 ∣ cOff) (hcfit : cOff + 8 * w.nl ≤ len)
    (h8m : 8 ∣ mOff) (hmfit : mOff + 8 * w.nl ≤ len)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 8 * w.nl ≤ len) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree →
      arithModPre w B rs1 pOff aOff bOff cOff mOff dOff rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (csrsRetProgram w.csr rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (arithModPost w aOff bOff cOff mOff dOff rf₀ ws₀ A₀)) :=
  csrs_handleS_sound entry w.csr rs1 ro B len
    (arithModPre w B rs1 pOff aOff bOff cOff mOff dOff)
    (fun ws => setBytes ws dOff (leBytesN w.nl (Accel.arith256Mod
        (wsNat w.nl ws aOff) (wsNat w.nl ws bOff)
        (wsNat w.nl ws cOff) (wsNat w.nl ws mOff))))
    (fun ws hws => by rw [length_setBytes]; exact hws)
    (fun rf₀ ws₀ hlen hex => by
      obtain ⟨A₀, hp, hpa, hpb, hpc, hpm, hpd, hmne⟩ := hex
      exact csrs_arithMod_spec_within w entry rs1 hrs1 B len ws₀ rf₀ hlen
        hrw.1 hrw.2.2 pOff aOff bOff cOff mOff dOff hp h8p hpfit h8a hafit
        h8b hbfit h8c hcfit h8m hmfit h8d hdfit hpa hpb hpc hpm hpd hmne)

/-- **The `nLimbs`-parametric Arith*Mod seam handle** (bead 4ch8f.11.6):
    `arithModHandle .w256 …` is the `0x802` 4-limb wrapper (the pilot's
    `arith256ModHandle`, re-derived generically), `arithModHandle .w384 …`
    the `0x80B` 6-limb one.  `ro` is the caller's read-only region
    (framed; the wrapper never touches it). -/
def arithModHandle (w : ArithWidth) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff aOff bOff cOff mOff dOff : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 40 ≤ len)
    (h8a : 8 ∣ aOff) (hafit : aOff + 8 * w.nl ≤ len)
    (h8b : 8 ∣ bOff) (hbfit : bOff + 8 * w.nl ≤ len)
    (h8c : 8 ∣ cOff) (hcfit : cOff + 8 * w.nl ≤ len)
    (h8m : 8 ∣ mOff) (hmfit : mOff + 8 * w.nl ≤ len)
    (h8d : 8 ∣ dOff) (hdfit : dOff + 8 * w.nl ≤ len) : FnHandleS where
  entry := entry
  code := CodeReq.ofProg entry (csrsRetProgram w.csr rs1)
  nSteps := 2
  region := ro
  rw := ⟨B, len⟩
  pre := arithModPre w B rs1 pOff aOff bOff cOff mOff dOff
  post := arithModPost w aOff bOff cOff mOff dOff
  sound := arithModHandle_sound w entry rs1 hrs1 ro B len hrw
    pOff aOff bOff cOff mOff dOff h8p hpfit h8a hafit h8b hbfit
    h8c hcfit h8m hmfit h8d hdfit

/-- The pilot's monomorphic precondition is the `.w256` instance of the
    generic one (contract agreement — `arith256ModHandle` and
    `arithModHandle .w256` are interchangeable at call sites). -/
theorem arithModPre_w256 (B : Word) (rs1 : Reg)
    (pOff aOff bOff cOff mOff dOff : Nat) :
    arithModPre .w256 B rs1 pOff aOff bOff cOff mOff dOff
      = arith256ModPre B rs1 pOff aOff bOff cOff mOff dOff := by
  funext rf ws A
  simp only [arithModPre, arith256ModPre, ArithWidth.nl, wsNat_four]

/-- The pilot's monomorphic postcondition is the `.w256` instance of the
    generic one. -/
theorem arithModPost_w256 (aOff bOff cOff mOff dOff : Nat) :
    arithModPost .w256 aOff bOff cOff mOff dOff
      = arith256ModPost aOff bOff cOff mOff dOff := by
  funext rf₀ ws₀ A₀ rf ws A
  simp only [arithModPost, arith256ModPost, ArithWidth.nl, wsNat_four,
    leBytes32_eq]

-- ============================================================================
-- The curve chord-addition handle (0x803 / 0x806 / 0x80C)
-- ============================================================================

/-- The `csrsValid` arm of a curve-add id (definitional). -/
private theorem csrsValid_curveAdd (c : CurveId) (s : MachineState)
    (rs1 : Reg) :
    s.csrsValid c.addCsr rs1
      = (MachineState.validDwordRange (s.getReg rs1) 2 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1)) (2 * c.nl) &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 8)) (2 * c.nl) &&
         Accel.ptValid c.p c.nl
           (s.readWords (s.getMem (s.getReg rs1)) (2 * c.nl)) &&
         Accel.ptValid c.p c.nl
           (s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * c.nl)) &&
         !(Accel.leLimbsToNat
             ((s.readWords (s.getMem (s.getReg rs1)) (2 * c.nl)).take c.nl)
           == Accel.leLimbsToNat
             ((s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * c.nl)).take c.nl)))
    := by
  cases c <;> rfl

/-- The `csrsWrite` arm of a curve-add id (definitional). -/
private theorem csrsWrite_curveAdd (c : CurveId) (s : MachineState)
    (rs1 : Reg) :
    s.csrsWrite c.addCsr rs1
      = (s.getMem (s.getReg rs1), Accel.curveAddL c.p c.nl
          (s.readWords (s.getMem (s.getReg rs1)) (2 * c.nl))
          (s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * c.nl))) := by
  cases c <;> rfl

/-- The curve chord-addition step: `csrs c.addCsr, rs1` with `rs1`
    pointing at a `[p1*, p2*]` parameter block; `p1` becomes
    `p1 + p2` by the chord formula (`Accel.curveAdd`) over the
    window-decoded coordinates.  Preconditions are exactly the
    accelerator's `csrsValid`: both points reduced (`ptValid`) and
    `x₁ ≠ x₂`. -/
theorem csrs_curveAdd_spec_within (c : CurveId)
    (base : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff q1Off q2Off : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8q1 : 8 ∣ q1Off) (hq1fit : q1Off + 16 * c.nl ≤ len)
    (h8q2 : 8 ∣ q2Off) (hq2fit : q2Off + 16 * c.nl ≤ len)
    (hp1 : wsDword ws pOff = B + BitVec.ofNat 64 q1Off)
    (hp2 : wsDword ws (pOff + 8) = B + BitVec.ofNat 64 q2Off)
    (hx1 : wsNat c.nl ws q1Off < c.p)
    (hy1 : wsNat c.nl ws (q1Off + 8 * c.nl) < c.p)
    (hx2 : wsNat c.nl ws q2Off < c.p)
    (hy2 : wsNat c.nl ws (q2Off + 8 * c.nl) < c.p)
    (hxne : wsNat c.nl ws q1Off ≠ wsNat c.nl ws q2Off) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS c.addCsr rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws q1Off (pairBytes c.nl (Accel.curveAdd c.p
          (wsNat c.nl ws q1Off) (wsNat c.nl ws (q1Off + 8 * c.nl))
          (wsNat c.nl ws q2Off) (wsNat c.nl ws (q2Off + 8 * c.nl)))))) := by
  have hmain := csrs_step_spec_within c.addCsr rs1 base B ws rf q1Off
    (Accel.natToLeLimbs c.nl (Accel.curveAdd c.p
        (wsNat c.nl ws q1Off) (wsNat c.nl ws (q1Off + 8 * c.nl))
        (wsNat c.nl ws q2Off) (wsNat c.nl ws (q2Off + 8 * c.nl))).1
      ++ Accel.natToLeLimbs c.nl (Accel.curveAdd c.p
        (wsNat c.nl ws q1Off) (wsNat c.nl ws (q1Off + 8 * c.nl))
        (wsNat c.nl ws q2Off) (wsNat c.nl ws (q2Off + 8 * c.nl))).2)
    h8q1
    (by rw [List.length_append, length_natToLeLimbs, length_natToLeLimbs]; omega)
    ?_
  · rw [flatMap_pairLimbs] at hmain
    exact hmain
  intro R s hPR
  rw [sepConj_assoc'] at hPR
  have hregs : s.getReg rs1 = rf.get rs1 :=
    holdsFor_regFileIs_getReg hPR hrs1
  have hMem := hPR
  rw [sepConj_left_comm] at hMem
  have hsrs1 : s.getReg rs1 = B + BitVec.ofNat 64 pOff := by rw [hregs, hp]
  have hslot : ∀ j : Nat, 8 ∣ j → j + 8 ≤ len →
      s.getMem (B + BitVec.ofNat 64 j) = wsDword ws j := fun j h8j hjfit =>
    holdsFor_bytesRegion_getMem hMem h8j (by omega)
  have hgP1 : s.getMem (s.getReg rs1) = B + BitVec.ofNat 64 q1Off := by
    rw [hsrs1, hslot pOff h8p (by omega), hp1]
  have hgP2 : s.getMem (s.getReg rs1 + 8) = B + BitVec.ofNat 64 q2Off := by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, hsrs1, add_ofNat_add,
      hslot (pOff + 8) (by omega) (by omega), hp2]
  have hrd1x : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1)) (2 * c.nl)).take c.nl)
      = wsNat c.nl ws q1Off := by
    rw [hgP1]; exact holdsFor_bytesRegion_readPair_fst hMem h8q1 (by omega)
  have hrd1y : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1)) (2 * c.nl)).drop c.nl)
      = wsNat c.nl ws (q1Off + 8 * c.nl) := by
    rw [hgP1]; exact holdsFor_bytesRegion_readPair_snd hMem h8q1 (by omega)
  have hrd2x : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * c.nl)).take c.nl)
      = wsNat c.nl ws q2Off := by
    rw [hgP2]; exact holdsFor_bytesRegion_readPair_fst hMem h8q2 (by omega)
  have hrd2y : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * c.nl)).drop c.nl)
      = wsNat c.nl ws (q2Off + 8 * c.nl) := by
    rw [hgP2]; exact holdsFor_bytesRegion_readPair_snd hMem h8q2 (by omega)
  have hvrange : ∀ (k n : Nat), 8 ∣ k → k + 8 * n ≤ len →
      MachineState.validDwordRange (B + BitVec.ofNat 64 k) n = true :=
    fun k n h8k hkfit => validDwordRange_of_window hb8 hvalid h8k hkfit
  refine ⟨?_, ?_⟩
  · rw [csrsValid_curveAdd c s rs1]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hsrs1]; exact hvrange pOff 2 h8p (by omega)
    · rw [hgP1]; exact hvrange q1Off (2 * c.nl) h8q1 (by omega)
    · rw [hgP2]; exact hvrange q2Off (2 * c.nl) h8q2 (by omega)
    · simp only [Accel.ptValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [hrd1x]; exact hx1, by rw [hrd1y]; exact hy1⟩
    · simp only [Accel.ptValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [hrd2x]; exact hx2, by rw [hrd2y]; exact hy2⟩
    · rw [hrd1x, hrd2x]; simpa using hxne
  · rw [csrsWrite_curveAdd c s rs1, curveAddL_decode,
      hrd1x, hrd1y, hrd2x, hrd2y, hgP1]

/-- Call-site obligation of a curve-add wrapper: `rs1` holds the
    `[p1*, p2*]` block pointer, both points decode to reduced coordinates,
    and `x₁ ≠ x₂` (the chord formula's domain — the accelerator traps
    otherwise, so callers case-split doubling/infinity in software). -/
def curveAddPre (c : CurveId) (B : Word) (rs1 : Reg)
    (pOff q1Off q2Off : Nat) : Reach :=
  fun rf ws _ =>
    rf.get rs1 = B + BitVec.ofNat 64 pOff
    ∧ wsDword ws pOff = B + BitVec.ofNat 64 q1Off
    ∧ wsDword ws (pOff + 8) = B + BitVec.ofNat 64 q2Off
    ∧ wsNat c.nl ws q1Off < c.p
    ∧ wsNat c.nl ws (q1Off + 8 * c.nl) < c.p
    ∧ wsNat c.nl ws q2Off < c.p
    ∧ wsNat c.nl ws (q2Off + 8 * c.nl) < c.p
    ∧ wsNat c.nl ws q1Off ≠ wsNat c.nl ws q2Off

/-- Snapshot-parameterized guarantee of a curve-add wrapper: `p1`'s
    buffer becomes `Accel.curveAdd` of the *entry* window's decoded
    points; registers and the ambient assertion untouched. -/
def curveAddPost (c : CurveId) (q1Off q2Off : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf = rf₀ ∧ A = A₀
    ∧ ws = setBytes ws₀ q1Off (pairBytes c.nl (Accel.curveAdd c.p
        (wsNat c.nl ws₀ q1Off) (wsNat c.nl ws₀ (q1Off + 8 * c.nl))
        (wsNat c.nl ws₀ q2Off) (wsNat c.nl ws₀ (q2Off + 8 * c.nl))))

/-- The curve-add handle's calling contract, standalone. -/
theorem curveAddHandle_sound (c : CurveId) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff q1Off q2Off : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8q1 : 8 ∣ q1Off) (hq1fit : q1Off + 16 * c.nl ≤ len)
    (h8q2 : 8 ∣ q2Off) (hq2fit : q2Off + 16 * c.nl ≤ len) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree →
      curveAddPre c B rs1 pOff q1Off q2Off rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (csrsRetProgram c.addCsr rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (curveAddPost c q1Off q2Off rf₀ ws₀ A₀)) :=
  csrs_handleS_sound entry c.addCsr rs1 ro B len
    (curveAddPre c B rs1 pOff q1Off q2Off)
    (fun ws => setBytes ws q1Off (pairBytes c.nl (Accel.curveAdd c.p
        (wsNat c.nl ws q1Off) (wsNat c.nl ws (q1Off + 8 * c.nl))
        (wsNat c.nl ws q2Off) (wsNat c.nl ws (q2Off + 8 * c.nl)))))
    (fun ws hws => by rw [length_setBytes]; exact hws)
    (fun rf₀ ws₀ hlen hex => by
      obtain ⟨A₀, hp, hp1, hp2, hx1, hy1, hx2, hy2, hxne⟩ := hex
      exact csrs_curveAdd_spec_within c entry rs1 hrs1 B len ws₀ rf₀ hlen
        hrw.1 hrw.2.2 pOff q1Off q2Off hp h8p hpfit h8q1 hq1fit h8q2 hq2fit
        hp1 hp2 hx1 hy1 hx2 hy2 hxne)

/-- **The curve chord-addition seam handle** (bead 4ch8f.11.6):
    secp256k1 `0x803`, BN254 `0x806`, BLS12-381 `0x80C`. -/
def curveAddHandle (c : CurveId) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff q1Off q2Off : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8q1 : 8 ∣ q1Off) (hq1fit : q1Off + 16 * c.nl ≤ len)
    (h8q2 : 8 ∣ q2Off) (hq2fit : q2Off + 16 * c.nl ≤ len) : FnHandleS where
  entry := entry
  code := CodeReq.ofProg entry (csrsRetProgram c.addCsr rs1)
  nSteps := 2
  region := ro
  rw := ⟨B, len⟩
  pre := curveAddPre c B rs1 pOff q1Off q2Off
  post := curveAddPost c q1Off q2Off
  sound := curveAddHandle_sound c entry rs1 hrs1 ro B len hrw
    pOff q1Off q2Off h8p hpfit h8q1 hq1fit h8q2 hq2fit

-- ============================================================================
-- The curve tangent-doubling handle (0x804 / 0x807 / 0x80D)
-- ============================================================================

/-- The `csrsValid` arm of a curve-dbl id (definitional).  Note the
    point is at `rs1` directly — no parameter block. -/
private theorem csrsValid_curveDbl (c : CurveId) (s : MachineState)
    (rs1 : Reg) :
    s.csrsValid c.dblCsr rs1
      = (MachineState.validDwordRange (s.getReg rs1) (2 * c.nl) &&
         Accel.ptValid c.p c.nl (s.readWords (s.getReg rs1) (2 * c.nl)) &&
         !(Accel.leLimbsToNat
             ((s.readWords (s.getReg rs1) (2 * c.nl)).drop c.nl) == 0)) := by
  cases c <;> rfl

/-- The `csrsWrite` arm of a curve-dbl id (definitional). -/
private theorem csrsWrite_curveDbl (c : CurveId) (s : MachineState)
    (rs1 : Reg) :
    s.csrsWrite c.dblCsr rs1
      = (s.getReg rs1, Accel.curveDblL c.p c.nl
          (s.readWords (s.getReg rs1) (2 * c.nl))) := by
  cases c <;> rfl

/-- The curve tangent-doubling step: `csrs c.dblCsr, rs1` with `rs1`
    pointing directly at the point, doubled in place by the tangent
    formula (`Accel.curveDbl`).  Preconditions are exactly the
    accelerator's `csrsValid`: reduced coordinates and `y ≠ 0`. -/
theorem csrs_curveDbl_spec_within (c : CurveId)
    (base : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (ptOff : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 ptOff)
    (h8pt : 8 ∣ ptOff) (hptfit : ptOff + 16 * c.nl ≤ len)
    (hx : wsNat c.nl ws ptOff < c.p)
    (hy : wsNat c.nl ws (ptOff + 8 * c.nl) < c.p)
    (hyne : wsNat c.nl ws (ptOff + 8 * c.nl) ≠ 0) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS c.dblCsr rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws ptOff (pairBytes c.nl (Accel.curveDbl c.p
          (wsNat c.nl ws ptOff) (wsNat c.nl ws (ptOff + 8 * c.nl)))))) := by
  have hmain := csrs_step_spec_within c.dblCsr rs1 base B ws rf ptOff
    (Accel.natToLeLimbs c.nl (Accel.curveDbl c.p
        (wsNat c.nl ws ptOff) (wsNat c.nl ws (ptOff + 8 * c.nl))).1
      ++ Accel.natToLeLimbs c.nl (Accel.curveDbl c.p
        (wsNat c.nl ws ptOff) (wsNat c.nl ws (ptOff + 8 * c.nl))).2)
    h8pt
    (by rw [List.length_append, length_natToLeLimbs, length_natToLeLimbs]; omega)
    ?_
  · rw [flatMap_pairLimbs] at hmain
    exact hmain
  intro R s hPR
  rw [sepConj_assoc'] at hPR
  have hregs : s.getReg rs1 = rf.get rs1 :=
    holdsFor_regFileIs_getReg hPR hrs1
  have hMem := hPR
  rw [sepConj_left_comm] at hMem
  have hsrs1 : s.getReg rs1 = B + BitVec.ofNat 64 ptOff := by rw [hregs, hp]
  have hrdx : Accel.leLimbsToNat
      ((s.readWords (s.getReg rs1) (2 * c.nl)).take c.nl)
      = wsNat c.nl ws ptOff := by
    rw [hsrs1]; exact holdsFor_bytesRegion_readPair_fst hMem h8pt (by omega)
  have hrdy : Accel.leLimbsToNat
      ((s.readWords (s.getReg rs1) (2 * c.nl)).drop c.nl)
      = wsNat c.nl ws (ptOff + 8 * c.nl) := by
    rw [hsrs1]; exact holdsFor_bytesRegion_readPair_snd hMem h8pt (by omega)
  have hvrange : ∀ (k n : Nat), 8 ∣ k → k + 8 * n ≤ len →
      MachineState.validDwordRange (B + BitVec.ofNat 64 k) n = true :=
    fun k n h8k hkfit => validDwordRange_of_window hb8 hvalid h8k hkfit
  refine ⟨?_, ?_⟩
  · rw [csrsValid_curveDbl c s rs1]
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hsrs1]; exact hvrange ptOff (2 * c.nl) h8pt (by omega)
    · simp only [Accel.ptValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [hrdx]; exact hx, by rw [hrdy]; exact hy⟩
    · rw [hrdy]; simpa using hyne
  · rw [csrsWrite_curveDbl c s rs1, curveDblL_decode, hrdx, hrdy, hsrs1]

/-- Call-site obligation of a curve-dbl wrapper: `rs1` points at the
    point, coordinates reduced, `y ≠ 0` (the tangent formula's domain —
    the accelerator traps on 2-torsion). -/
def curveDblPre (c : CurveId) (B : Word) (rs1 : Reg) (ptOff : Nat) : Reach :=
  fun rf ws _ =>
    rf.get rs1 = B + BitVec.ofNat 64 ptOff
    ∧ wsNat c.nl ws ptOff < c.p
    ∧ wsNat c.nl ws (ptOff + 8 * c.nl) < c.p
    ∧ wsNat c.nl ws (ptOff + 8 * c.nl) ≠ 0

/-- Snapshot-parameterized guarantee of a curve-dbl wrapper: the point's
    buffer becomes `Accel.curveDbl` of the *entry* window's decoded
    point. -/
def curveDblPost (c : CurveId) (ptOff : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf = rf₀ ∧ A = A₀
    ∧ ws = setBytes ws₀ ptOff (pairBytes c.nl (Accel.curveDbl c.p
        (wsNat c.nl ws₀ ptOff) (wsNat c.nl ws₀ (ptOff + 8 * c.nl))))

/-- The curve-dbl handle's calling contract, standalone. -/
theorem curveDblHandle_sound (c : CurveId) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (ptOff : Nat) (h8pt : 8 ∣ ptOff) (hptfit : ptOff + 16 * c.nl ≤ len) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree →
      curveDblPre c B rs1 ptOff rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (csrsRetProgram c.dblCsr rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (curveDblPost c ptOff rf₀ ws₀ A₀)) :=
  csrs_handleS_sound entry c.dblCsr rs1 ro B len
    (curveDblPre c B rs1 ptOff)
    (fun ws => setBytes ws ptOff (pairBytes c.nl (Accel.curveDbl c.p
        (wsNat c.nl ws ptOff) (wsNat c.nl ws (ptOff + 8 * c.nl)))))
    (fun ws hws => by rw [length_setBytes]; exact hws)
    (fun rf₀ ws₀ hlen hex => by
      obtain ⟨A₀, hp, hx, hy, hyne⟩ := hex
      exact csrs_curveDbl_spec_within c entry rs1 hrs1 B len ws₀ rf₀ hlen
        hrw.1 hrw.2.2 ptOff hp h8pt hptfit hx hy hyne)

/-- **The curve tangent-doubling seam handle** (bead 4ch8f.11.6):
    secp256k1 `0x804`, BN254 `0x807`, BLS12-381 `0x80D`. -/
def curveDblHandle (c : CurveId) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (ptOff : Nat) (h8pt : 8 ∣ ptOff)
    (hptfit : ptOff + 16 * c.nl ≤ len) : FnHandleS where
  entry := entry
  code := CodeReq.ofProg entry (csrsRetProgram c.dblCsr rs1)
  nSteps := 2
  region := ro
  rw := ⟨B, len⟩
  pre := curveDblPre c B rs1 ptOff
  post := curveDblPost c ptOff
  sound := curveDblHandle_sound c entry rs1 hrs1 ro B len hrw
    ptOff h8pt hptfit

-- ============================================================================
-- The Fp2 ("complex") op handle (0x808/9/A, 0x80E/F/810)
-- ============================================================================

/-- The `csrsValid` arm of an Fp2-op id (definitional; the machine
    dispatch groups the three ops of a family into one arm). -/
private theorem csrsValid_cx (f : Fp2Id) (o : CxOp) (s : MachineState)
    (rs1 : Reg) :
    s.csrsValid (f.csr o) rs1
      = (MachineState.validDwordRange (s.getReg rs1) 2 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1)) (2 * f.nl) &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 8)) (2 * f.nl) &&
         Accel.ptValid f.p f.nl
           (s.readWords (s.getMem (s.getReg rs1)) (2 * f.nl)) &&
         Accel.ptValid f.p f.nl
           (s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * f.nl))) := by
  cases f <;> cases o <;> rfl

/-- The `csrsWrite` arm of an Fp2-op id (definitional). -/
private theorem csrsWrite_cx (f : Fp2Id) (o : CxOp) (s : MachineState)
    (rs1 : Reg) :
    s.csrsWrite (f.csr o) rs1
      = (s.getMem (s.getReg rs1), o.opL f.p f.nl
          (s.readWords (s.getMem (s.getReg rs1)) (2 * f.nl))
          (s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * f.nl))) := by
  cases f <;> cases o <;> rfl

/-- The Fp2-op step: `csrs (f.csr o), rs1` with `rs1` pointing at an
    `[f1*, f2*]` parameter block; `f1` becomes `f1 ∘ f2` (`CxOp.op`,
    `u² = −1`) over the window-decoded component pairs.  Preconditions
    are exactly the accelerator's `csrsValid`: both operands
    component-reduced. -/
theorem csrs_cx_spec_within (f : Fp2Id) (o : CxOp)
    (base : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff q1Off q2Off : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8q1 : 8 ∣ q1Off) (hq1fit : q1Off + 16 * f.nl ≤ len)
    (h8q2 : 8 ∣ q2Off) (hq2fit : q2Off + 16 * f.nl ≤ len)
    (hp1 : wsDword ws pOff = B + BitVec.ofNat 64 q1Off)
    (hp2 : wsDword ws (pOff + 8) = B + BitVec.ofNat 64 q2Off)
    (hx1 : wsNat f.nl ws q1Off < f.p)
    (hy1 : wsNat f.nl ws (q1Off + 8 * f.nl) < f.p)
    (hx2 : wsNat f.nl ws q2Off < f.p)
    (hy2 : wsNat f.nl ws (q2Off + 8 * f.nl) < f.p) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS (f.csr o) rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws q1Off (pairBytes f.nl (o.op f.p
          (wsNat f.nl ws q1Off, wsNat f.nl ws (q1Off + 8 * f.nl))
          (wsNat f.nl ws q2Off, wsNat f.nl ws (q2Off + 8 * f.nl)))))) := by
  have hmain := csrs_step_spec_within (f.csr o) rs1 base B ws rf q1Off
    (Accel.natToLeLimbs f.nl (o.op f.p
        (wsNat f.nl ws q1Off, wsNat f.nl ws (q1Off + 8 * f.nl))
        (wsNat f.nl ws q2Off, wsNat f.nl ws (q2Off + 8 * f.nl))).1
      ++ Accel.natToLeLimbs f.nl (o.op f.p
        (wsNat f.nl ws q1Off, wsNat f.nl ws (q1Off + 8 * f.nl))
        (wsNat f.nl ws q2Off, wsNat f.nl ws (q2Off + 8 * f.nl))).2)
    h8q1
    (by rw [List.length_append, length_natToLeLimbs, length_natToLeLimbs]; omega)
    ?_
  · rw [flatMap_pairLimbs] at hmain
    exact hmain
  intro R s hPR
  rw [sepConj_assoc'] at hPR
  have hregs : s.getReg rs1 = rf.get rs1 :=
    holdsFor_regFileIs_getReg hPR hrs1
  have hMem := hPR
  rw [sepConj_left_comm] at hMem
  have hsrs1 : s.getReg rs1 = B + BitVec.ofNat 64 pOff := by rw [hregs, hp]
  have hslot : ∀ j : Nat, 8 ∣ j → j + 8 ≤ len →
      s.getMem (B + BitVec.ofNat 64 j) = wsDword ws j := fun j h8j hjfit =>
    holdsFor_bytesRegion_getMem hMem h8j (by omega)
  have hgP1 : s.getMem (s.getReg rs1) = B + BitVec.ofNat 64 q1Off := by
    rw [hsrs1, hslot pOff h8p (by omega), hp1]
  have hgP2 : s.getMem (s.getReg rs1 + 8) = B + BitVec.ofNat 64 q2Off := by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, hsrs1, add_ofNat_add,
      hslot (pOff + 8) (by omega) (by omega), hp2]
  have hrd1x : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1)) (2 * f.nl)).take f.nl)
      = wsNat f.nl ws q1Off := by
    rw [hgP1]; exact holdsFor_bytesRegion_readPair_fst hMem h8q1 (by omega)
  have hrd1y : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1)) (2 * f.nl)).drop f.nl)
      = wsNat f.nl ws (q1Off + 8 * f.nl) := by
    rw [hgP1]; exact holdsFor_bytesRegion_readPair_snd hMem h8q1 (by omega)
  have hrd2x : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * f.nl)).take f.nl)
      = wsNat f.nl ws q2Off := by
    rw [hgP2]; exact holdsFor_bytesRegion_readPair_fst hMem h8q2 (by omega)
  have hrd2y : Accel.leLimbsToNat
      ((s.readWords (s.getMem (s.getReg rs1 + 8)) (2 * f.nl)).drop f.nl)
      = wsNat f.nl ws (q2Off + 8 * f.nl) := by
    rw [hgP2]; exact holdsFor_bytesRegion_readPair_snd hMem h8q2 (by omega)
  have hvrange : ∀ (k n : Nat), 8 ∣ k → k + 8 * n ≤ len →
      MachineState.validDwordRange (B + BitVec.ofNat 64 k) n = true :=
    fun k n h8k hkfit => validDwordRange_of_window hb8 hvalid h8k hkfit
  refine ⟨?_, ?_⟩
  · rw [csrsValid_cx f o s rs1]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hsrs1]; exact hvrange pOff 2 h8p (by omega)
    · rw [hgP1]; exact hvrange q1Off (2 * f.nl) h8q1 (by omega)
    · rw [hgP2]; exact hvrange q2Off (2 * f.nl) h8q2 (by omega)
    · simp only [Accel.ptValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [hrd1x]; exact hx1, by rw [hrd1y]; exact hy1⟩
    · simp only [Accel.ptValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by rw [hrd2x]; exact hx2, by rw [hrd2y]; exact hy2⟩
  · rw [csrsWrite_cx f o s rs1, cxOp_complexL,
      hrd1x, hrd1y, hrd2x, hrd2y, hgP1]

/-- Call-site obligation of an Fp2-op wrapper: `rs1` holds the
    `[f1*, f2*]` block pointer and both operands decode to reduced
    components. -/
def cxPre (f : Fp2Id) (B : Word) (rs1 : Reg)
    (pOff q1Off q2Off : Nat) : Reach :=
  fun rf ws _ =>
    rf.get rs1 = B + BitVec.ofNat 64 pOff
    ∧ wsDword ws pOff = B + BitVec.ofNat 64 q1Off
    ∧ wsDword ws (pOff + 8) = B + BitVec.ofNat 64 q2Off
    ∧ wsNat f.nl ws q1Off < f.p
    ∧ wsNat f.nl ws (q1Off + 8 * f.nl) < f.p
    ∧ wsNat f.nl ws q2Off < f.p
    ∧ wsNat f.nl ws (q2Off + 8 * f.nl) < f.p

/-- Snapshot-parameterized guarantee of an Fp2-op wrapper: `f1`'s
    buffer becomes `CxOp.op` of the *entry* window's decoded pairs. -/
def cxPost (f : Fp2Id) (o : CxOp) (q1Off q2Off : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf = rf₀ ∧ A = A₀
    ∧ ws = setBytes ws₀ q1Off (pairBytes f.nl (o.op f.p
        (wsNat f.nl ws₀ q1Off, wsNat f.nl ws₀ (q1Off + 8 * f.nl))
        (wsNat f.nl ws₀ q2Off, wsNat f.nl ws₀ (q2Off + 8 * f.nl))))

/-- The Fp2-op handle's calling contract, standalone. -/
theorem cxHandle_sound (f : Fp2Id) (o : CxOp) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff q1Off q2Off : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8q1 : 8 ∣ q1Off) (hq1fit : q1Off + 16 * f.nl ≤ len)
    (h8q2 : 8 ∣ q2Off) (hq2fit : q2Off + 16 * f.nl ≤ len) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree →
      cxPre f B rs1 pOff q1Off q2Off rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (csrsRetProgram (f.csr o) rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (cxPost f o q1Off q2Off rf₀ ws₀ A₀)) :=
  csrs_handleS_sound entry (f.csr o) rs1 ro B len
    (cxPre f B rs1 pOff q1Off q2Off)
    (fun ws => setBytes ws q1Off (pairBytes f.nl (o.op f.p
        (wsNat f.nl ws q1Off, wsNat f.nl ws (q1Off + 8 * f.nl))
        (wsNat f.nl ws q2Off, wsNat f.nl ws (q2Off + 8 * f.nl)))))
    (fun ws hws => by rw [length_setBytes]; exact hws)
    (fun rf₀ ws₀ hlen hex => by
      obtain ⟨A₀, hp, hp1, hp2, hx1, hy1, hx2, hy2⟩ := hex
      exact csrs_cx_spec_within f o entry rs1 hrs1 B len ws₀ rf₀ hlen
        hrw.1 hrw.2.2 pOff q1Off q2Off hp h8p hpfit h8q1 hq1fit h8q2 hq2fit
        hp1 hp2 hx1 hy1 hx2 hy2)

/-- **The Fp2-op seam handle** (bead 4ch8f.11.6): BN254
    `0x808/0x809/0x80A`, BLS12-381 `0x80E/0x80F/0x810` — add/sub/mul
    with `u² = −1`. -/
def cxHandle (f : Fp2Id) (o : CxOp) (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff q1Off q2Off : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8q1 : 8 ∣ q1Off) (hq1fit : q1Off + 16 * f.nl ≤ len)
    (h8q2 : 8 ∣ q2Off) (hq2fit : q2Off + 16 * f.nl ≤ len) : FnHandleS where
  entry := entry
  code := CodeReq.ofProg entry (csrsRetProgram (f.csr o) rs1)
  nSteps := 2
  region := ro
  rw := ⟨B, len⟩
  pre := cxPre f B rs1 pOff q1Off q2Off
  post := cxPost f o q1Off q2Off
  sound := cxHandle_sound f o entry rs1 hrs1 ro B len hrw
    pOff q1Off q2Off h8p hpfit h8q1 hq1fit h8q2 hq2fit

-- ============================================================================
-- The Sha256f compression handle (0x805)
-- ============================================================================

/-- The `n`-dword window slice at byte offset `k` — the `List Word` view
    `readWords` decodes over a framed window
    (`holdsFor_bytesRegion_readWords`).  The Sha256f operands are dword
    LISTS (u32-packed state/block), not `wsNat` naturals. -/
def wsDwords (n : Nat) (ws : List (BitVec 8)) (k : Nat) : List Word :=
  (List.range n).map fun i => wsDword ws (k + 8 * i)

@[simp] theorem length_wsDwords (n : Nat) (ws : List (BitVec 8)) (k : Nat) :
    (wsDwords n ws k).length = n := by
  simp [wsDwords]

/-- Reading a dword slice strictly below a splice is unchanged. -/
theorem wsDwords_setBytes_low {n : Nat} {bs ns : List (BitVec 8)} {j k : Nat}
    (h : k + 8 * n ≤ j) :
    wsDwords n (setBytes bs j ns) k = wsDwords n bs k := by
  unfold wsDwords
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact wsDword_setBytes_low (by omega)

/-- Reading a dword slice entirely above a splice is unchanged. -/
theorem wsDwords_setBytes_high {n : Nat} {bs ns : List (BitVec 8)} {j k : Nat}
    (h : j + ns.length ≤ k) :
    wsDwords n (setBytes bs j ns) k = wsDwords n bs k := by
  unfold wsDwords
  apply List.map_congr_left
  intro i hi
  exact wsDword_setBytes_high (by omega)

/-- Decoding a freshly spliced dword payload recovers it (the dword-list
    sibling of `wsNat_setBytes_leBytesN`). -/
theorem wsDwords_setBytes_flatMap {bs : List (BitVec 8)} {j : Nat}
    {payload : List Word} (hfit : j + 8 * payload.length ≤ bs.length) :
    wsDwords payload.length (setBytes bs j (payload.flatMap dwordBytes)) j
      = payload := by
  have hslot : ((setBytes bs j (payload.flatMap dwordBytes)).drop j).take
      (8 * payload.length) = payload.flatMap dwordBytes := by
    have := setBytes_slot bs (payload.flatMap dwordBytes) j
      (by rw [length_flatMap_dwordBytes]; omega)
    rwa [length_flatMap_dwordBytes] at this
  have hlimb : ∀ t : Nat, t < payload.length →
      wsDword (setBytes bs j (payload.flatMap dwordBytes)) (j + 8 * t)
        = payload.getD t 0 := by
    intro t ht
    unfold wsDword
    have hs8 : (((setBytes bs j (payload.flatMap dwordBytes)).drop j).drop
        (8 * t)).take 8 = ((payload.flatMap dwordBytes).drop (8 * t)).take 8 := by
      conv_rhs => rw [← hslot]
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
    rw [show j + 8 * t = j + (8 * t) from rfl, ← List.drop_drop, hs8,
      flatMap_dwordBytes_slice payload t ht, packBytes_dwordBytes]
  unfold wsDwords
  rw [List.map_congr_left (fun i hi => hlimb i (List.mem_range.mp hi))]
  exact map_getD_range payload 0

/-- The compressed state the Sha256f accelerator writes back, as dwords:
    the REAL `Accel.sha256Compress` over the u32 views of the window's
    8-u32 state slice (at `stOff`) and 16-u32 block slice (at `inOff`). -/
def sha256Dwords (ws : List (BitVec 8)) (stOff inOff : Nat) : List Word :=
  Accel.u32sToDwords (Accel.sha256Compress
    (Accel.dwordsToU32s (wsDwords 4 ws stOff))
    (Accel.dwordsToU32s (wsDwords 8 ws inOff)))

@[simp] theorem length_sha256Dwords (ws : List (BitVec 8)) (stOff inOff : Nat) :
    (sha256Dwords ws stOff inOff).length = 4 := by
  have h8 : (Accel.dwordsToU32s (wsDwords 4 ws stOff)).length = 8 := by
    rw [Accel.length_dwordsToU32s, length_wsDwords]
  rw [sha256Dwords, Accel.length_u32sToDwords,
    Accel.sha256Compress_length _ _ (by omega)]

/-- The 32-byte wire image of the compressed state. -/
def sha256Bytes (ws : List (BitVec 8)) (stOff inOff : Nat) : List (BitVec 8) :=
  (sha256Dwords ws stOff inOff).flatMap dwordBytes

@[simp] theorem length_sha256Bytes (ws : List (BitVec 8)) (stOff inOff : Nat) :
    (sha256Bytes ws stOff inOff).length = 32 := by
  rw [sha256Bytes, length_flatMap_dwordBytes, length_sha256Dwords]

/-- The `csrsValid` arm selected by CSR id `0x805` (definitional). -/
private theorem csrsValid_sha256 (s : MachineState) (rs1 : Reg) :
    s.csrsValid 0x805 rs1
      = (MachineState.validDwordRange (s.getReg rs1) 2 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1)) 4 &&
         MachineState.validDwordRange (s.getMem (s.getReg rs1 + 8)) 8) := rfl

/-- The `csrsWrite` arm selected by CSR id `0x805` (definitional). -/
private theorem csrsWrite_sha256 (s : MachineState) (rs1 : Reg) :
    s.csrsWrite 0x805 rs1
      = (s.getMem (s.getReg rs1), Accel.u32sToDwords (Accel.sha256Compress
          (Accel.dwordsToU32s (s.readWords (s.getMem (s.getReg rs1)) 4))
          (Accel.dwordsToU32s
            (s.readWords (s.getMem (s.getReg rs1 + 8)) 8)))) := rfl

/-- The Sha256f compression step: `csrs 0x805, rs1` with `rs1` pointing
    at a `[state*, input*]` parameter block whose two pointers land inside
    the window; the 32-byte state buffer becomes the REAL
    `Accel.sha256Compress` of the entry window's decoded state/block
    (`sha256Dwords`), and nothing else moves — not even a register.
    Preconditions are exactly the accelerator's `csrsValid` (the operand
    blocks are valid dword ranges; Sha256f has no value-domain guard). -/
theorem csrs_sha256Compress_spec_within
    (base : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff stOff inOff : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8st : 8 ∣ stOff) (hstfit : stOff + 32 ≤ len)
    (h8in : 8 ∣ inOff) (hinfit : inOff + 64 ≤ len)
    (hpst : wsDword ws pOff = B + BitVec.ofNat 64 stOff)
    (hpin : wsDword ws (pOff + 8) = B + BitVec.ofNat 64 inOff) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS 0x805 rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws stOff (sha256Bytes ws stOff inOff))) := by
  have hmain := csrs_step_spec_within 0x805 rs1 base B ws rf stOff
    (sha256Dwords ws stOff inOff) h8st
    (by rw [length_sha256Dwords]; omega) ?_
  · rw [show (sha256Dwords ws stOff inOff).flatMap dwordBytes
        = sha256Bytes ws stOff inOff from rfl] at hmain
    exact hmain
  intro R s hPR
  rw [sepConj_assoc'] at hPR
  have hregs : s.getReg rs1 = rf.get rs1 :=
    holdsFor_regFileIs_getReg hPR hrs1
  have hMem := hPR
  rw [sepConj_left_comm] at hMem
  have hsrs1 : s.getReg rs1 = B + BitVec.ofNat 64 pOff := by rw [hregs, hp]
  have hslot : ∀ j : Nat, 8 ∣ j → j + 8 ≤ len →
      s.getMem (B + BitVec.ofNat 64 j) = wsDword ws j := fun j h8j hjfit =>
    holdsFor_bytesRegion_getMem hMem h8j (by omega)
  have hgSt : s.getMem (s.getReg rs1) = B + BitVec.ofNat 64 stOff := by
    rw [hsrs1, hslot pOff h8p (by omega), hpst]
  have hgIn : s.getMem (s.getReg rs1 + 8) = B + BitVec.ofNat 64 inOff := by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, hsrs1, add_ofNat_add,
      hslot (pOff + 8) (by omega) (by omega), hpin]
  have hrdSt : s.readWords (s.getMem (s.getReg rs1)) 4
      = wsDwords 4 ws stOff := by
    rw [hgSt, holdsFor_bytesRegion_readWords hMem 4 stOff h8st (by omega)]
    rfl
  have hrdIn : s.readWords (s.getMem (s.getReg rs1 + 8)) 8
      = wsDwords 8 ws inOff := by
    rw [hgIn, holdsFor_bytesRegion_readWords hMem 8 inOff h8in (by omega)]
    rfl
  have hvrange : ∀ (k n : Nat), 8 ∣ k → k + 8 * n ≤ len →
      MachineState.validDwordRange (B + BitVec.ofNat 64 k) n = true :=
    fun k n h8k hkfit => validDwordRange_of_window hb8 hvalid h8k hkfit
  refine ⟨?_, ?_⟩
  · rw [csrsValid_sha256 s rs1]
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hsrs1]; exact hvrange pOff 2 h8p (by omega)
    · rw [hgSt]; exact hvrange stOff 4 h8st (by omega)
    · rw [hgIn]; exact hvrange inOff 8 h8in (by omega)
  · rw [csrsWrite_sha256 s rs1, hrdSt, hrdIn, hgSt]
    rfl

/-- The Sha256f wrapper triple in the C-ABI calling shape
    (`FnHandleS.sound`'s core): one compression, then `jalr x0, ra, 0` —
    back at `ret` in 2 steps with the state buffer rewritten and
    everything else (registers, the rest of the window, the ambient `A`)
    intact. -/
theorem csrs_sha256Compress_ret_spec
    (entry : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff stOff inOff : Nat)
    (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8st : 8 ∣ stOff) (hstfit : stOff + 32 ≤ len)
    (h8in : 8 ∣ inOff) (hinfit : inOff + 64 ≤ len)
    (hpst : wsDword ws pOff = B + BitVec.ofNat 64 stOff)
    (hpin : wsDword ws (pOff + 8) = B + BitVec.ofNat 64 inOff)
    (A : Assertion) (hA : A.pcFree)
    (ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 2 entry ret
      (CodeReq.ofProg entry (csrsRetProgram 0x805 rs1))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B ws) ** A))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B
        (setBytes ws stOff (sha256Bytes ws stOff inOff))) ** A)) :=
  csrs_ret_spec_of_step
    (csrs_sha256Compress_spec_within entry rs1 hrs1 B len ws rf hwslen hb8
      hvalid pOff stOff inOff hp h8p hpfit h8st hstfit h8in hinfit hpst hpin)
    A hA ret halign

/-- Call-site obligation of the Sha256f wrapper: `rs1` holds the
    `[state*, input*]` block pointer and the two pointers land at the
    given window offsets.  No value-domain conditions — the accelerator's
    `csrsValid` only checks the operand ranges.  The static side
    conditions (alignment, fit) live in the handle constructor. -/
def sha256CompressPre (B : Word) (rs1 : Reg)
    (pOff stOff inOff : Nat) : Reach :=
  fun rf ws _ =>
    rf.get rs1 = B + BitVec.ofNat 64 pOff
    ∧ wsDword ws pOff = B + BitVec.ofNat 64 stOff
    ∧ wsDword ws (pOff + 8) = B + BitVec.ofNat 64 inOff

/-- Snapshot-parameterized guarantee of the Sha256f wrapper: the state
    buffer becomes `Accel.sha256Compress` of the *entry* window's decoded
    state/block; registers and the ambient assertion untouched. -/
def sha256CompressPost (stOff inOff : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf = rf₀ ∧ A = A₀
    ∧ ws = setBytes ws₀ stOff (sha256Bytes ws₀ stOff inOff)

/-- The Sha256f handle's calling contract, standalone. -/
theorem sha256CompressHandle_sound (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff stOff inOff : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8st : 8 ∣ stOff) (hstfit : stOff + 32 ≤ len)
    (h8in : 8 ∣ inOff) (hinfit : inOff + 64 ≤ len) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree →
      sha256CompressPre B rs1 pOff stOff inOff rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (csrsRetProgram 0x805 rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (sha256CompressPost stOff inOff rf₀ ws₀ A₀)) :=
  csrs_handleS_sound entry 0x805 rs1 ro B len
    (sha256CompressPre B rs1 pOff stOff inOff)
    (fun ws => setBytes ws stOff (sha256Bytes ws stOff inOff))
    (fun ws hws => by rw [length_setBytes]; exact hws)
    (fun rf₀ ws₀ hlen hex => by
      obtain ⟨A₀, hp, hpst, hpin⟩ := hex
      exact csrs_sha256Compress_spec_within entry rs1 hrs1 B len ws₀ rf₀ hlen
        hrw.1 hrw.2.2 pOff stOff inOff hp h8p hpfit h8st hstfit h8in hinfit
        hpst hpin)

/-- **The Sha256f seam handle** (bead 4ch8f.18.1): the `csrs 0x805, rs1`
    compression wrapper packaged as a snapshot-parameterized callee, in
    the same shape as `arithModHandle`/`curveDblHandle`.  Unblocks the
    `zkvm_sha256` port (bead 4ch8f.18) and the sha256/keccak
    accelerator-consumer family.  `ro` is the caller's read-only region
    (framed; the wrapper never touches it). -/
def sha256CompressHandle (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff stOff inOff : Nat)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 16 ≤ len)
    (h8st : 8 ∣ stOff) (hstfit : stOff + 32 ≤ len)
    (h8in : 8 ∣ inOff) (hinfit : inOff + 64 ≤ len) : FnHandleS where
  entry := entry
  code := CodeReq.ofProg entry (csrsRetProgram 0x805 rs1)
  nSteps := 2
  region := ro
  rw := ⟨B, len⟩
  pre := sha256CompressPre B rs1 pOff stOff inOff
  post := sha256CompressPost stOff inOff
  sound := sha256CompressHandle_sound entry rs1 hrs1 ro B len hrw
    pOff stOff inOff h8p hpfit h8st hstfit h8in hinfit

end SAsm
end EvmAsm.Rv64
