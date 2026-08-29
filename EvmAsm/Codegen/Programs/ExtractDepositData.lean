/-
  EvmAsm.Codegen.Programs.ExtractDepositData

  `extract_deposit_data` (bead 8uld3.1, EIP-6110) — strip the Solidity ABI framing
  from a DepositEvent log payload and return the concatenated raw fields:
  pubkey(48) || withdrawal_credentials(32) || amount(8) || signature(96) || index(8)
  = 192 bytes, the per-deposit body the consensus layer consumes.

  Mirrors execution-specs amsterdam requests.py:extract_deposit_data. Every
  well-formed DepositEvent payload is exactly 576 bytes with a FIXED ABI layout:
    head: 5 x 32-byte big-endian offsets = 160, 256, 320, 384, 512
    each field: 32-byte big-endian size (= 48,32,8,96,8) then the data, 32-padded
  Any deviation => InvalidBlock (a misbehaving deposit contract), so this returns a
  nonzero status rather than silently accepting unexpected data.

  Self-contained (no external callees). The full parse_deposit_requests (scan the
  block receipts for deposit-contract logs and concatenate extract_deposit_data over
  each) composes this once receipts are materialized from execution — that scan is
  the execution-gated remainder of 8uld3.1.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.EddBe32EqSAsm
import EvmAsm.Codegen.Programs.EddMemcpySAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## extract_deposit_data
    a0 = DepositEvent data ptr   a1 = data byte length   a2 = 192-byte out ptr
    a0 (output) = 0 ok / 1 malformed (bad length / offset / size). -/
-- Drift guard (build-time evaluation): the exact rendering of the verified
-- `edd_memcpy` program.  The assemble+cmp byte-identity check against the
-- previous hand-written text was run against THIS string; if the emitter or
-- the program changes, this pin fails and the check must be rerun.
#guard emitProgram EddMemcpySAsm.eddMemcpy_prog ==
  "  beq x12, x0, .+28\n  lbu x5, 0(x10)\n  sb x5, 0(x11)\n"
    ++ "  addi x10, x10, 1\n  addi x11, x11, 1\n  addi x12, x12, -1\n"
    ++ "  jal x0, .-24\n  jalr x0, 0(x1)"

-- Drift guard (build-time evaluation): the exact rendering of the verified
-- `edd_be32_eq` program.  The assemble+cmp byte-identity check against the
-- previous hand-written text was run against THIS string; if the emitter or
-- the program changes, this pin fails and the check must be rerun.
#guard emitProgram EddBe32EqSAsm.eddBe32Eq_prog ==
  "  li x5, 0\n  li x6, 28\n  beq x5, x6, .+24\n  add x7, x10, x5\n"
    ++ "  lbu x28, 0(x7)\n  bne x28, x0, .+64\n  addi x5, x5, 1\n"
    ++ "  jal x0, .-24\n  lbu x6, 28(x10)\n  slli x6, x6, 24\n"
    ++ "  lbu x7, 29(x10)\n  slli x7, x7, 16\n  or x6, x6, x7\n"
    ++ "  lbu x7, 30(x10)\n  slli x7, x7, 8\n  or x6, x6, x7\n"
    ++ "  lbu x7, 31(x10)\n  or x6, x6, x7\n  bne x6, x11, .+12\n"
    ++ "  li x10, 1\n  jalr x0, 0(x1)\n  li x10, 0\n  jalr x0, 0(x1)"

/-- The `extract_deposit_data` main body as an instruction list (#12989):
    frame prologue, the 576-byte length guard, ten `edd_be32_eq` checks
    (five canonical ABI offsets, five field sizes) sharing one fail tail,
    five `edd_memcpy` field extractions, and the shared epilogue.  The
    cross-entry `jal ra` targets are the numeric offsets of the two
    verified leaves inside the emitted unit (`edd_be32_eq` at instruction
    index 76, `edd_memcpy` at 99).  Byte-identity with the previous
    label-form text checked by assemble+cmp (428 bytes, whole unit). -/
def extractDepositData_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x12,
    .LI .x5 (576 : Word),
    .BNE .x11 .x5 (252 : BitVec 13),
    .MV .x10 .x8,
    .LI .x11 (160 : Word),
    .JAL .x1 (264 : BitVec 21),
    .BEQ .x10 .x0 (236 : BitVec 13),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .LI .x11 (256 : Word),
    .JAL .x1 (248 : BitVec 21),
    .BEQ .x10 .x0 (220 : BitVec 13),
    .ADDI .x10 .x8 (64 : BitVec 12),
    .LI .x11 (320 : Word),
    .JAL .x1 (232 : BitVec 21),
    .BEQ .x10 .x0 (204 : BitVec 13),
    .ADDI .x10 .x8 (96 : BitVec 12),
    .LI .x11 (384 : Word),
    .JAL .x1 (216 : BitVec 21),
    .BEQ .x10 .x0 (188 : BitVec 13),
    .ADDI .x10 .x8 (128 : BitVec 12),
    .LI .x11 (512 : Word),
    .JAL .x1 (200 : BitVec 21),
    .BEQ .x10 .x0 (172 : BitVec 13),
    .ADDI .x10 .x8 (160 : BitVec 12),
    .LI .x11 (48 : Word),
    .JAL .x1 (184 : BitVec 21),
    .BEQ .x10 .x0 (156 : BitVec 13),
    .ADDI .x10 .x8 (256 : BitVec 12),
    .LI .x11 (32 : Word),
    .JAL .x1 (168 : BitVec 21),
    .BEQ .x10 .x0 (140 : BitVec 13),
    .ADDI .x10 .x8 (320 : BitVec 12),
    .LI .x11 (8 : Word),
    .JAL .x1 (152 : BitVec 21),
    .BEQ .x10 .x0 (124 : BitVec 13),
    .ADDI .x10 .x8 (384 : BitVec 12),
    .LI .x11 (96 : Word),
    .JAL .x1 (136 : BitVec 21),
    .BEQ .x10 .x0 (108 : BitVec 13),
    .ADDI .x10 .x8 (512 : BitVec 12),
    .LI .x11 (8 : Word),
    .JAL .x1 (120 : BitVec 21),
    .BEQ .x10 .x0 (92 : BitVec 13),
    .ADDI .x10 .x8 (192 : BitVec 12),
    .MV .x11 .x9,
    .LI .x12 (48 : Word),
    .JAL .x1 (192 : BitVec 21),
    .ADDI .x10 .x8 (288 : BitVec 12),
    .ADDI .x11 .x9 (48 : BitVec 12),
    .LI .x12 (32 : Word),
    .JAL .x1 (176 : BitVec 21),
    .ADDI .x10 .x8 (352 : BitVec 12),
    .ADDI .x11 .x9 (80 : BitVec 12),
    .LI .x12 (8 : Word),
    .JAL .x1 (160 : BitVec 21),
    .ADDI .x10 .x8 (416 : BitVec 12),
    .ADDI .x11 .x9 (88 : BitVec 12),
    .LI .x12 (96 : Word),
    .JAL .x1 (144 : BitVec 21),
    .ADDI .x10 .x8 (544 : BitVec 12),
    .ADDI .x11 .x9 (184 : BitVec 12),
    .LI .x12 (8 : Word),
    .JAL .x1 (128 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

#guard (extractDepositData_prog : List Instr).length = 76

/-- The full three-entry emitted unit. -/
def extractDepositDataBundle_prog : Program :=
  (extractDepositData_prog : List Instr)
    ++ (EddBe32EqSAsm.eddBe32Eq_prog : List Instr)
    ++ (EddMemcpySAsm.eddMemcpy_prog : List Instr)

#guard (extractDepositDataBundle_prog : List Instr).length = 107

def extractDepositDataFunction : String :=
  -- The whole unit is emitted from the shared instruction lists
  -- (`extractDepositDataBundle_prog`); byte-identity with the previous
  -- label-form text checked by assemble+cmp (428 bytes).  The internal
  -- fail/ret labels and the cross-entry `jal ra, edd_*` calls became
  -- numeric offsets.
  "extract_deposit_data:\n" ++
  emitProgram extractDepositData_prog ++ "\n" ++
  -- a0=ptr to 32-byte BE field, a1=K (<2^32); a0=1 if value==K else 0.
  -- Emitted from the verified DCode program (`EddBe32EqSAsm.eddDeriv`,
  -- spec `eddBe32Eq_retSpec`).
  "edd_be32_eq:\n" ++
  emitProgram EddBe32EqSAsm.eddBe32Eq_prog ++ "\n" ++
  -- a0=src, a1=dst, a2=len (leaf, byte-wise).  Emitted from the verified
  -- DCode program (`EddMemcpySAsm.mcDeriv`, spec `eddMemcpy_retSpec`);
  -- call-site premises discharged in this file (#12805).
  "edd_memcpy:\n" ++
  emitProgram EddMemcpySAsm.eddMemcpy_prog

/-! ## Consuming `eddMemcpy_retSpec` at the call sites (#12805)

    `eddMemcpy_retSpec` is gated on `mcStatic`, whose disjointness
    disjunct was a docstring claim about "the deployed callers".  This
    section makes it a theorem: at each of the FIVE `edd_memcpy` call
    sites above (pubkey/wc/amount/sig/index), the source is inside the
    576-byte DepositEvent arena and the destination inside the 192-byte
    output arena, and the arenas the deployed probe passes are concrete
    and disjoint.  `eddMemcpy_callsite_spec` discharges the whole
    `mcStatic` conjunction (and both region well-formednesses, whose
    dword-alignment demand every site meets — all five src offsets
    192/288/352/416/544 and dst offsets 0/48/80/88/184 are 8-aligned)
    from those addresses, yielding a triple whose pre/post do not
    mention `mcStatic` at all. -/

section EddMemcpyCallSites

open EvmAsm.Rv64.SAsm

/-- The probe's DepositEvent data arena: `a0` after the ziskemu length
    wrapper (`0x40000000 + 16`), 576 bytes, inside the input window. -/
def eddDataPtr : Word := 0x40000010

/-- The probe's output arena: the 192-byte unframed deposit at
    `OUTPUT + 8` (`0xa0010008`), inside writable RAM. -/
def eddOutPtr : Word := 0xa0010008

/-- `mcStatic` discharged from the concrete arenas: any copy of `n`
    bytes from offset `offS` of the data arena to offset `offD` of the
    output arena satisfies every conjunct — bounds, no wrap, and
    disjointness (the data arena ends at `0x40000250`, far below the
    output arena at `0xa0010008`). -/
theorem edd_arena_mcStatic (offS offD n : Nat) (bs ws0 : List (BitVec 8))
    (hbs : n ≤ bs.length) (hw : ws0.length = n)
    (hS : offS + n ≤ 576) (hD : offD + n ≤ 192) :
    EddMemcpySAsm.mcStatic (eddDataPtr + BitVec.ofNat 64 offS)
      (eddOutPtr + BitVec.ofNat 64 offD) bs ws0 n := by
  unfold EddMemcpySAsm.mcStatic eddDataPtr eddOutPtr
  refine ⟨hbs, hw, by omega, ?_, ?_, Or.inl ?_⟩ <;> bv_omega

/-- Wrap-free three-term address arithmetic in the single-mod form
    `omega` handles (nested `ofNat` additions otherwise split into
    independent mod variables it cannot tie together). -/
theorem edd_toNat_add3 (x : Word) (a k : Nat)
    (hx : x.toNat + a + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 a + BitVec.ofNat 64 k).toNat
      = x.toNat + a + k := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Two-term version of `edd_toNat_add3`. -/
theorem edd_toNat_add2 (x : Word) (a : Nat)
    (hx : x.toNat + a < 2 ^ 64) :
    (x + BitVec.ofNat 64 a).toNat = x.toNat + a := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The source region of a call-site copy is well-formed: 8-aligned
    (all five source offsets are multiples of 8 off the 8-aligned data
    pointer) and inside the valid input window. -/
theorem edd_src_region_wf (offS n : Nat) (bs : List (BitVec 8))
    (hbs : bs.length = n) (h8 : offS % 8 = 0) (hS : offS + n ≤ 576) :
    Region.wf ⟨eddDataPtr + BitVec.ofNat 64 offS, bs⟩ := by
  have hbase : eddDataPtr.toNat = 0x40000010 := by decide
  have h2 : (eddDataPtr + BitVec.ofNat 64 offS).toNat
      = 0x40000010 + offS := by
    rw [edd_toNat_add2 _ _ (by rw [hbase]; omega), hbase]
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · show (eddDataPtr + BitVec.ofNat 64 offS).toNat % 8 = 0
    rw [h2]; omega
  · show (eddDataPtr + BitVec.ofNat 64 offS).toNat + bs.length < 2 ^ 64
    rw [h2, hbs]; omega
  · have hk' : k < bs.length := hk
    rw [hbs] at hk'
    have haddr : (eddDataPtr + BitVec.ofNat 64 offS
          + BitVec.ofNat 64 k).toNat = 0x40000010 + offS + k := by
      rw [edd_toNat_add3 _ _ _ (by rw [hbase]; omega), hbase]
    show isValidMemAddr (eddDataPtr + BitVec.ofNat 64 offS
      + BitVec.ofNat 64 k) = true
    simp only [isValidMemAddr, haddr, EvmAsm.Rv64.MEM_START,
      EvmAsm.Rv64.MEM_END, EvmAsm.Rv64.INPUT_MEM_START,
      EvmAsm.Rv64.INPUT_MEM_END, EvmAsm.Rv64.RAM_MEM_START,
      EvmAsm.Rv64.RAM_MEM_END, decide_eq_true_eq, Bool.and_eq_true,
      Bool.or_eq_true]
    omega

/-- The destination region of a call-site copy is well-formed:
    8-aligned (all five destination offsets are multiples of 8 off the
    8-aligned output pointer) and inside writable RAM. -/
theorem edd_out_region_wf (offD n : Nat)
    (h8 : offD % 8 = 0) (hD : offD + n ≤ 192) :
    RwRegion.wf ⟨eddOutPtr + BitVec.ofNat 64 offD, n⟩ := by
  have hbase : eddOutPtr.toNat = 0xa0010008 := by decide
  have h2 : (eddOutPtr + BitVec.ofNat 64 offD).toNat
      = 0xa0010008 + offD := by
    rw [edd_toNat_add2 _ _ (by rw [hbase]; omega), hbase]
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · show (eddOutPtr + BitVec.ofNat 64 offD).toNat % 8 = 0
    rw [h2]; omega
  · show (eddOutPtr + BitVec.ofNat 64 offD).toNat + n < 2 ^ 64
    rw [h2]; omega
  · have hk' : k < n := hk
    have haddr : (eddOutPtr + BitVec.ofNat 64 offD
          + BitVec.ofNat 64 k).toNat = 0xa0010008 + offD + k := by
      rw [edd_toNat_add3 _ _ _ (by rw [hbase]; omega), hbase]
    show isValidMemAddr (eddOutPtr + BitVec.ofNat 64 offD
      + BitVec.ofNat 64 k) = true
    simp only [isValidMemAddr, haddr, EvmAsm.Rv64.MEM_START,
      EvmAsm.Rv64.MEM_END, EvmAsm.Rv64.INPUT_MEM_START,
      EvmAsm.Rv64.INPUT_MEM_END, EvmAsm.Rv64.RAM_MEM_START,
      EvmAsm.Rv64.RAM_MEM_END, decide_eq_true_eq, Bool.and_eq_true,
      Bool.or_eq_true]
    omega

/-- The consumed call-site triple at `(offS, offD, n)`: the copy spec
    with `mcStatic` GONE from both pre and post — it holds at the site,
    so the caller no longer owes it. -/
def EddMemcpyCallSite (offS offD n : Nat) : Prop :=
  ∀ (bs ws0 : List (BitVec 8)) (base ret : Word),
    bs.length = n → ws0.length = n → (ret &&& ~~~(1 : Word)) = ret →
    cpsTripleWithin
      (EddMemcpySAsm.mcDeriv (eddDataPtr + BitVec.ofNat 64 offS)
        (eddOutPtr + BitVec.ofNat 64 offD) bs ws0 n).stmt.steps base ret
      (CodeReq.ofProg base
        ((EddMemcpySAsm.mcDeriv (eddDataPtr + BitVec.ofNat 64 offS)
          (eddOutPtr + BitVec.ofNat 64 offD) bs ws0 n).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM ⟨eddDataPtr + BitVec.ofNat 64 offS, bs⟩
            ⟨eddOutPtr + BitVec.ofNat 64 offD, n⟩
          (fun rf ws A =>
            rf.get .x10 = eddDataPtr + BitVec.ofNat 64 offS ∧
            rf.get .x11 = eddOutPtr + BitVec.ofNat 64 offD ∧
            rf.get .x12 = BitVec.ofNat 64 n ∧ ws = ws0 ∧
            A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM ⟨eddDataPtr + BitVec.ofNat 64 offS, bs⟩
            ⟨eddOutPtr + BitVec.ofNat 64 offD, n⟩
          (fun _ ws A => ws = bs.take n ∧ A = empAssertion))

/-- `eddMemcpy_retSpec` consumed: at any call site whose offsets are
    8-aligned and whose copy stays inside the two arenas, the spec's
    every premise (`mcStatic` including disjointness, and both region
    well-formednesses) is discharged from the concrete addresses. -/
theorem eddMemcpy_callsite_spec (offS offD n : Nat)
    (h8S : offS % 8 = 0) (h8D : offD % 8 = 0)
    (hS : offS + n ≤ 576) (hD : offD + n ≤ 192) :
    EddMemcpyCallSite offS offD n := by
  intro bs ws0 base ret hbs hw halign
  have hst := edd_arena_mcStatic offS offD n bs ws0 (by omega) hw hS hD
  exact cpsTripleWithin_weaken
    (sepConj_mono_right (asrtM_mono (fun rf ws A h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hst, h.2.2.2.2⟩)))
    (sepConj_mono_right (asrtM_mono (fun rf ws A h => ⟨h.1, h.2.2⟩)))
    (EddMemcpySAsm.eddMemcpy_retSpec _ _ bs ws0 n base ret
      (edd_src_region_wf offS n bs hbs h8S hS)
      (edd_out_region_wf offD n h8D hD) halign)

/-- Site 1: `pubkey` — `data+192 → out[0]`, 48 bytes. -/
theorem eddMemcpy_pubkey_callsite : EddMemcpyCallSite 192 0 48 :=
  eddMemcpy_callsite_spec 192 0 48 rfl rfl (by decide) (by decide)

/-- Site 2: `withdrawal_credentials` — `data+288 → out[48]`, 32 bytes. -/
theorem eddMemcpy_wc_callsite : EddMemcpyCallSite 288 48 32 :=
  eddMemcpy_callsite_spec 288 48 32 rfl rfl (by decide) (by decide)

/-- Site 3: `amount` — `data+352 → out[80]`, 8 bytes. -/
theorem eddMemcpy_amount_callsite : EddMemcpyCallSite 352 80 8 :=
  eddMemcpy_callsite_spec 352 80 8 rfl rfl (by decide) (by decide)

/-- Site 4: `signature` — `data+416 → out[88]`, 96 bytes. -/
theorem eddMemcpy_sig_callsite : EddMemcpyCallSite 416 88 96 :=
  eddMemcpy_callsite_spec 416 88 96 rfl rfl (by decide) (by decide)

/-- Site 5: `index` — `data+544 → out[184]`, 8 bytes. -/
theorem eddMemcpy_index_callsite : EddMemcpyCallSite 544 184 8 :=
  eddMemcpy_callsite_spec 544 184 8 rfl rfl (by decide) (by decide)

end EddMemcpyCallSites

/-- `zisk_extract_deposit_data`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes 8..16 : data length (so the check can exercise the length guard)
      bytes 16..  : the DepositEvent data payload
    Output: bytes 0..8 = status; bytes 8..200 = the 192-byte unframed deposit. -/
def ziskExtractDepositDataPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # data len\n" ++
  "  addi a0, a5, 16             # data ptr\n" ++
  "  li a2, 0xa0010008           # 192-byte out (OUTPUT + 8)\n" ++
  "  jal ra, extract_deposit_data\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Ledd_pdone\n" ++
  extractDepositDataFunction ++ "\n" ++
  ".Ledd_pdone:"


end EvmAsm.Codegen
