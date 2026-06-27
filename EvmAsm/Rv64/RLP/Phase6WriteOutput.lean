/-
  EvmAsm.Rv64.RLP.Phase6WriteOutput

  EL.3 / Phase 6 — the pipeline's output half. The `write_output` syscall appends
  `readBytes ptr size` (byte-granular) to the public output; the decoder leaves its result as a
  `bytesRegion` (dword-packed). This file bridges them — `readBytes_of_bytesRegion`: when
  `bytesRegion base bs` holds, `readBytes base bs.length = bs` — the keystone connecting the
  decoder's output region to what `write_output` emits.
-/

import EvmAsm.Rv64.RLP.Phase6ReadDecode
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- `bytesRegion` is PC-free — lets `runBlock`/`pcFree` discharge frame side-conditions. -/
instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/-- **A byte read from a held `bytesRegion`.** When `bytesRegion regionBase bs ** R` holds in `s`
    (region dword-aligned, byte `i` in range, no address overflow), `s.getByte (regionBase + i)`
    is `bs[i]` — the `holdsFor`-level byte read underlying `bytesRegion_lbu_within`. -/
theorem getByte_of_bytesRegion (regionBase : Word) (bs : List (BitVec 8)) (i : Nat)
    (R : Assertion) (s : MachineState)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (h : (bytesRegion regionBase bs ** R).holdsFor s) :
    s.getByte (regionBase + BitVec.ofNat 64 i) = bs[i]'hi := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, _hf, _hr, heq⟩ := bytesRegion_dword_at regionBase bs (i / 8) hq
  rw [heq] at h
  have hmem : s.getMem (regionBase + BitVec.ofNat 64 (8 * (i / 8)))
      = packBytes ((bs.drop (8 * (i / 8))).take 8) :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left h)))
  unfold MachineState.getByte
  rw [alignToDword_add_ofNat_of_aligned halign hover, hmem,
      byteOffset_add_ofNat_of_aligned halign hover,
      extractByte_packBytes _ _ (by omega)
        (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- **`readBytes` reads back a held `bytesRegion`.** When `bytesRegion base bs ** R` holds in `s`
    (dword-aligned, no overflow), reading `bs.length` bytes from `base` returns `bs`. The bridge
    connecting the decoder's `bytesRegion` output to what `write_output` (which uses `readBytes`)
    emits. -/
theorem readBytes_of_bytesRegion (base : Word) (bs : List (BitVec 8)) (R : Assertion)
    (s : MachineState)
    (halign : base.toNat % 8 = 0) (hover : base.toNat + bs.length < 2 ^ 64)
    (h : (bytesRegion base bs ** R).holdsFor s) :
    s.readBytes base bs.length = bs := by
  -- Generalised: reading `n` bytes from offset `off` returns `(bs.drop off).take n`.
  have key : ∀ n off, off + n ≤ bs.length →
      s.readBytes (base + BitVec.ofNat 64 off) n = (bs.drop off).take n := by
    intro n
    induction n with
    | zero => intro off _; simp
    | succ m ih =>
      intro off hoff
      have hoff' : off < bs.length := by omega
      rw [MachineState.readBytes_succ,
          getByte_of_bytesRegion base bs off R s halign hoff' (by omega) h,
          show (base + BitVec.ofNat 64 off) + 1 = base + BitVec.ofNat 64 (off + 1) from by bv_omega,
          ih (off + 1) (by omega),
          List.drop_eq_getElem_cons hoff', List.take_succ_cons]
  have := key bs.length 0 (by omega)
  rwa [show base + BitVec.ofNat 64 0 = base from by bv_omega, List.drop_zero,
      List.take_length] at this

-- ============================================================================
-- Step 57 — `publicValues`-append `holdsFor` framing (the write-half analogue of
-- `holdsFor_sepConj_memIs_setMem`). These thread the host `write_output` effect
-- (an append to the public-values stream) through a separation-logic frame.
-- ============================================================================

/-- If a partial state doesn't own the public values, then appending to the
    public-values stream preserves compatibility (the `appendPublicValues`
    analogue of `PartialState.CompatibleWith_setMem`). -/
theorem compatibleWith_appendPublicValues {h : PartialState} {s : MachineState}
    {bytes : List (BitVec 8)} (hcompat : h.CompatibleWith s) (hnone : h.publicValues = none) :
    h.CompatibleWith (s.appendPublicValues bytes) := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi, hib⟩ := hcompat
  refine ⟨fun r' v' hv => by rw [MachineState.getReg_appendPublicValues]; exact hr r' v' hv,
         fun a' v' hv => by rw [MachineState.getMem_appendPublicValues]; exact hm a' v' hv,
         fun a' i' hv => by rw [MachineState.code_appendPublicValues]; exact hc a' i' hv,
         fun v' hv => by rw [MachineState.pc_appendPublicValues]; exact hpc v' hv,
         fun v' hv => ?_,
         fun v' hv => by rw [MachineState.privateInput_appendPublicValues]; exact hpi v' hv,
         fun v' hv => by rw [MachineState.inputBufBase_appendPublicValues]; exact hib v' hv⟩
  rw [hnone] at hv; simp at hv

/-- **`publicValues`-append framing.** If `publicValuesIs vals ** R` holds for `s`, then
    `publicValuesIs (vals ++ extra) ** R` holds for `s.appendPublicValues extra`. The frame `R`
    is preserved because it's disjoint from the public-values stream being appended to. This is
    the `publicValues`-update analogue of `holdsFor_sepConj_memIs_setMem`. -/
theorem holdsFor_sepConj_publicValuesIs_appendPublicValues {vals extra : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : (publicValuesIs vals ** R).holdsFor s) :
    (publicValuesIs (vals ++ extra) ** R).holdsFor (s.appendPublicValues extra) := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [publicValuesIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own the public values (from disjointness)
  have ha2 : h2.publicValues = none := by
    rcases hdisj.2.2.2.2.1 with h | h
    · simp [PartialState.singletonPublicValues] at h
    · exact h
  -- Split old compatibility; the singleton half pins `s.publicValues = vals`
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  have hsv : s.publicValues = vals := hc1.2.2.2.2.1 vals rfl
  -- Disjointness preserved (same ownership shape, only the public-values payload changes)
  have hdisj' : (PartialState.singletonPublicValues (vals ++ extra)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, Or.inr ha2,
     hdisj.2.2.2.2.2.1, hdisj.2.2.2.2.2.2⟩
  -- singletonPublicValues (vals ++ extra) compatible with s.appendPublicValues extra
  have hc1' : (PartialState.singletonPublicValues (vals ++ extra)).CompatibleWith
      (s.appendPublicValues extra) := by
    refine ⟨fun r w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun a w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun a i hw => by simp [PartialState.singletonPublicValues] at hw,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun w hw => ?_,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw⟩
    simp only [PartialState.singletonPublicValues, Option.some.injEq] at hw
    subst hw; simp [hsv]
  -- h2 compatible with s.appendPublicValues extra (doesn't own publicValues)
  have hc2' : h2.CompatibleWith (s.appendPublicValues extra) :=
    compatibleWith_appendPublicValues hc2 ha2
  exact ⟨(PartialState.singletonPublicValues (vals ++ extra)).union h2,
         (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
         PartialState.singletonPublicValues (vals ++ extra), h2, hdisj', rfl, rfl, hh2⟩

-- ============================================================================
-- Step 58 — CPS-level `write_output` ECALL spec (zkvm-standards C ABI: t0 = 0x10).
-- The `read_input` analogue is `ecall_read_input_spec_gen_within`. The host effect
-- (`writeOutput ptr size = appendPublicValues (readBytes ptr size.toNat)`) is folded
-- in via the `readBytes_of_bytesRegion` bridge: when the source is a held `bytesRegion`,
-- the appended bytes are exactly `bs`.
-- ============================================================================

/-- `write_output` (zkvm-standards C ABI, t0 = 0x10) appends `readBytes ptr size` to the
    public-values stream. When the source `[ptr, ptr+bs.length)` is a held `bytesRegion ptr bs`
    (dword-aligned, no overflow) and `x11 = bs.length`, the emitted bytes are exactly `bs`, so
    `publicValuesIs old` advances to `publicValuesIs (old ++ bs)`. The region itself is unchanged.

    Pre:  x5 = 0x10; x10 = ptr; x11 = bs.length; bytesRegion ptr bs; publicValuesIs old
    Post: (same regs/region); publicValuesIs (old ++ bs) -/
theorem ecall_write_output_spec_gen_within
    (ptr : Word) (bs old : List (BitVec 8)) (addr : Word)
    (halign : ptr.toNat % 8 = 0) (hover : ptr.toNat + bs.length < 2 ^ 64) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr .ECALL)
      ((addr ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0x10)) **
        (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (BitVec.ofNat 64 bs.length)) **
        bytesRegion ptr bs ** publicValuesIs old)
      ((addr ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0x10)) **
        (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ (BitVec.ofNat 64 bs.length)) **
        bytesRegion ptr bs ** publicValuesIs (old ++ bs)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL :=
    CodeReq.singleton_satisfiedBy.mp hcr
  -- Extract x5/x10/x11
  have hBIG := holdsFor_sepConj_elim_left hPR
  have hr1 := holdsFor_sepConj_elim_right hBIG
  have hx5 : s.getReg .x5 = BitVec.ofNat 64 0x10 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hr1)
  have hr2 := holdsFor_sepConj_elim_right hr1
  have hx10 : s.getReg .x10 = ptr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hr2)
  have hr3 := holdsFor_sepConj_elim_right hr2
  have hx11 : s.getReg .x11 = BitVec.ofNat 64 bs.length :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hr3)
  -- The bytes read back from the held region are exactly `bs`.
  have hregion : (bytesRegion ptr bs **
      ((s.pc ↦ᵢ .ECALL) ** (.x5 ↦ᵣ BitVec.ofNat 64 0x10) **
        (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ BitVec.ofNat 64 bs.length) **
        publicValuesIs old ** R)).holdsFor s := by
    simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hPR
  have hread : s.readBytes ptr bs.length = bs :=
    readBytes_of_bytesRegion ptr bs _ s halign hover hregion
  -- Execute the ECALL: appends `readBytes ptr (ofNat bs.length).toNat = bs`.
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hstep := step_ecall_write_output hfetch hx5
  rw [hx10, hx11] at hstep
  simp only [MachineState.writeOutput, htoNat, hread] at hstep
  refine ⟨1, Nat.le_refl 1, (s.appendPublicValues bs).setPC (s.pc + 4),
    ?_, by simp [MachineState.setPC], ?_⟩
  · show (step s).bind (stepN 0) = some _
    simp only [hstep, stepN, Option.bind_some]
  · -- POST: advance publicValues via the framing lemma, then setPC.
    have hPR' : (publicValuesIs old **
          ((s.pc ↦ᵢ .ECALL) ** (.x5 ↦ᵣ BitVec.ofNat 64 0x10) **
           (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ BitVec.ofNat 64 bs.length) **
           bytesRegion ptr bs ** R)).holdsFor s := by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hPR
    have h1 := holdsFor_sepConj_publicValuesIs_appendPublicValues (extra := bs) hPR'
    -- h1 : (publicValuesIs (old ++ bs) ** REST).holdsFor (s.appendPublicValues bs)
    have hPOST : (((s.pc ↦ᵢ .ECALL) **
          (.x5 ↦ᵣ BitVec.ofNat 64 0x10) **
          (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ BitVec.ofNat 64 bs.length) **
          bytesRegion ptr bs ** publicValuesIs (old ++ bs)) ** R).holdsFor
          (s.appendPublicValues bs) := by
      simpa only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] using h1
    refine holdsFor_pcFree_setPC (pcFree_sepConj ?_ hR) hPOST
    apply pcFree_sepConj pcFree_instrAt
    apply pcFree_sepConj pcFree_regIs
    apply pcFree_sepConj pcFree_regIs
    apply pcFree_sepConj pcFree_regIs
    exact pcFree_sepConj (bytesRegion_pcFree _ _) pcFree_publicValuesIs

-- ============================================================================
-- Step 59 — `write_output` wrapper (ADDI + LI + LI + ECALL): move the output base
-- into x10, load the length into x11 and the 0x10 selector into x5, then ECALL.
-- The `read_input` analogue is `rlp_phase4_read_input_len_spec_within_exact`.
-- ============================================================================

/-- `write_output` wrapper program: `ADDI x10, rOut, 0` (x10 := output base), `LI x11, size`
    (x11 := output length), `LI x5, 0x10` (write_output selector), `ECALL`. -/
def rlp_phase6_write_output_prog (rOut : Reg) (size : Word) : Program :=
  [.ADDI .x10 rOut 0,
   .LI   .x11 size,
   .LI   .x5  (BitVec.ofNat 64 0x10),
   .ECALL]

theorem rlp_phase6_write_output_code_eq_ofProg
    (rOut : Reg) (size : Word) (base : Word) :
    CodeReq.ofProg base (rlp_phase6_write_output_prog rOut size) =
      (CodeReq.singleton base (.ADDI .x10 rOut 0)).union
        ((CodeReq.singleton (base + 4) (.LI .x11 size)).union
          ((CodeReq.singleton (base + 4 + 4) (.LI .x5 (BitVec.ofNat 64 0x10))).union
            (CodeReq.singleton (base + 4 + 4 + 4) .ECALL))) := by
  simp only [rlp_phase6_write_output_prog, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]

/-- `write_output` Phase-6 wrapper spec: four-instruction wrapper that emits the held output
    region `bytesRegion outBase out` to the public output via `write_output` (t0=0x10).

    Pre:  rOut = outBase; x10/x11/x5 caller-owned; (base+12) ↦ᵢ .ECALL;
          bytesRegion outBase out; publicValuesIs old.
    Post: x10 = outBase; x11 = out.length; x5 = 0x10; region unchanged;
          publicValuesIs (old ++ out). -/
theorem rlp_phase6_write_output_spec_within_exact
    (rOut : Reg) (outBase : Word) (out old : List (BitVec 8))
    (v10 v11 v5 : Word) (base : Word)
    (halign : outBase.toNat % 8 = 0) (hover : outBase.toNat + out.length < 2 ^ 64) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base (rlp_phase6_write_output_prog rOut (BitVec.ofNat 64 out.length)))
      ((rOut ↦ᵣ outBase) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) **
        (base + 12 ↦ᵢ .ECALL) **
        bytesRegion outBase out ** publicValuesIs old)
      ((rOut ↦ᵣ outBase) **
        (.x10 ↦ᵣ outBase) **
        (.x11 ↦ᵣ (BitVec.ofNat 64 out.length)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0x10)) **
        (base + 12 ↦ᵢ .ECALL) **
        bytesRegion outBase out ** publicValuesIs (old ++ out)) := by
  rw [rlp_phase6_write_output_code_eq_ofProg]
  have haddi1 := addi_spec_gen_within .x10 rOut v10 outBase (0 : BitVec 12) base (by nofun)
  rw [show outBase + signExtend12 (0 : BitVec 12) = outBase from by
    rw [AddrNorm.se12_0]; bv_omega] at haddi1
  have hli2 := li_spec_gen_within .x11 v11 (BitVec.ofNat 64 out.length) (base + 4) (by nofun)
  have hli3 := li_spec_gen_within .x5 v5 (BitVec.ofNat 64 0x10) (base + 8) (by nofun)
  have hecall_base := ecall_write_output_spec_gen_within outBase out old (base + 4 + 4 + 4)
    halign hover
  have hecall := cpsTripleWithin_frameR ((rOut ↦ᵣ outBase)) (by pcFree) hecall_base
  runBlock haddi1 hli2 hli3 hecall

end EvmAsm.Rv64.RLP
