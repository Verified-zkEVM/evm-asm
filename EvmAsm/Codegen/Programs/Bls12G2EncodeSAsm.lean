/-
  EvmAsm.Codegen.Programs.Bls12G2EncodeSAsm

  **The first count-up call-loop port** (beads evm-asm-ipt7m +
  evm-asm-4ch8f.58.3.24.2): `blsg2_encode`, byte-TRANSPARENT — the emitted
  `blsg2Encode_prog` IS an `abiFrameProg (-40)/(+40)` flatten with frame
  `[(ra,0),(s0,8),(s1,16),(s2,24)]` and a 12-instruction body:

      blsg2_encode:  addi sp, sp, -40 ; sd ra/s0/s1/s2
                     mv   s0, a0            -- src (4 × 48-byte LE field elements)
                     mv   s1, a1            -- dst (4 × 48-byte BE output record)
                     li   s2, 0             -- i := 0
             loop:   slli t0, s2, 4
                     slli t1, s2, 5
                     add  t0, t0, t1        -- t0 := 48·i
                     add  a0, s0, t0
                     add  a1, s1, t0
                     jal  ra, blsg_le_to_be -- encode element i (clobbers ra!)
                     addi s2, s2, 1         -- i := i+1
                     li   t0, 4
                     bne  s2, t0, loop      -- count-up to the bound 4
                     ld … ; addi sp, sp, 40 ; ret

  The loop is discharged by the new `countupLoopBottom_spec` (count-up to a
  nonzero bound, bottom-tested, body contains the cross-call); the callee
  contract is DERIVED from `Bls12G1LeToBeSAsm.blsgLeToBeFn_spec` by the
  flat-contract adapter (`Fn.retSpecFlat`) — no hand-written callee proof.

  **Genuine post** (`blsg2Encode_spec`): on return `sp`, `ra` (clobbered by
  four real `jal`s), `s0`, `s1`, `s2` are restored to ENTRY values, and the
  4 × 48-byte output record holds the big-endian encodings of the four input
  field elements — chunk `k` of `[dst, dst+192)` equals
  `blsgLeToBeBytes in_k` — with the four input chunks untouched.
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.Bls12G2
import EvmAsm.Codegen.Programs.Bls12G1LeToBeSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open Bls12G1LeToBeSAsm (blsgLeToBeFn blsgLeToBeFn_spec blsgLeToBeBytes)

namespace Bls12G2EncodeSAsm

-- ============================================================================
-- Anchors and byte-ties (semantic constants vs address anchors — guide §9).
-- ============================================================================

-- Semantic constants: 4 elements × 48 bytes.
-- Address anchors (`#guard`-tied to the live GuestAddrs):
#guard GuestAddrs.blsg2_encode = 0x8003405c
#guard GuestAddrs.blsg_le_to_be = 0x8002f3c4

/-- The caller's 4-slot frame: `ra`, `s0`, `s1`, `s2` (the loop counter is
    callee-saved — it must survive the callee's exposed-register clobber). -/
def encFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]

/-- The single-exit body: pointer copies, counter init, the count-up call
    loop. -/
def encBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .LI .x18 (0 : Word),
    .SLLI .x5 .x18 (4 : BitVec 6),
    .SLLI .x6 .x18 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x10 .x8 .x5,
    .ADD .x11 .x9 .x5,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg2_encode + 52)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .LI .x5 (4 : Word),
    .BNE .x18 .x5 (-32 : BitVec 13) ]

-- Byte-transparency: the emitted routine IS the abiFrameProg flatten.
#guard abiFrameProg (-40 : BitVec 12) (40 : BitVec 12) encFrame encBody
  = blsg2Encode_prog

/-- Byte-transparency, kernel-checked. -/
theorem encProg_eq :
    abiFrameProg (-40 : BitVec 12) (40 : BitVec 12) encFrame encBody
      = blsg2Encode_prog := rfl

/-- The verification `CodeReq`: the caller at its guest address plus the
    callee at its guest address (non-adjacent — a genuine cross-module
    call). -/
def encCr : CodeReq :=
  (CodeReq.ofProg (0x80033eb8 : Word) blsg2Encode_prog).union
    (CodeReq.ofProg (0x8002f220 : Word) blsgLeToBe_prog)

-- ============================================================================
-- Word helpers.
-- ============================================================================

private theorem addr_fold (b : Word) (i j : Nat) :
    (b + BitVec.ofNat 64 i) + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      Nat.mod_eq_of_lt x.isLt]

private theorem cnt_step_up (n : Nat) (_h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 n + signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 (n + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem ofNat_shl (i k m : Nat) (hm : 2 ^ k = m) (h : m * i < 2 ^ 64) :
    (BitVec.ofNat 64 i) <<< k = BitVec.ofNat 64 (m * i) := by
  subst hm
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hilt : i < 2 ^ 64 := by
    have : i ≤ 2 ^ k * i := Nat.le_mul_of_pos_left i hkpos
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hilt, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by rw [Nat.mul_comm] at h; exact h),
      Nat.mod_eq_of_lt h, Nat.mul_comm]

private theorem toNat_add_ofNat (b : Word) (i : Nat) (h : b.toNat + i < 2 ^ 64) :
    (b + BitVec.ofNat 64 i).toNat = b.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

-- ============================================================================
-- The callee's flat contract, derived by the adapter (`Fn.retSpecFlat`).
-- ============================================================================

/-- The exposed registers other than `a0`/`a1` — the callee owns the whole
    exposed file (that is what its `Fn.Spec` claims). -/
def leScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Split the full exposed file into the `a0`/`a1` atoms plus the scratch. -/
private theorem exposedRegs_split2 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf leScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [leScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_leScratch : (.x10 : Reg) ∉ leScratch := by decide
private theorem x11_notin_leScratch : (.x11 : Reg) ∉ leScratch := by decide

/-- **The flat whole-routine contract for `blsg_le_to_be`**, DERIVED from
    `blsgLeToBeFn_spec` by `Fn.retSpecFlat`: entered at its guest address
    with any aligned return address in `ra`, source/destination pointers in
    `a0`/`a1`, ownership of the remaining exposed registers, the 48-byte
    output window, and the (framed) 48-byte input region, it returns with
    the output window holding the big-endian encoding `blsgLeToBeBytes inb`
    and `ra` intact.  The callee step count stays SYMBOLIC (guide §5a). -/
theorem blsgLeToBeFlat_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 48) (holen : ob.length = 48)
    (hwfR : Region.wf ⟨srci, inb⟩) (hwfW : RwRegion.wf ⟨dsti, 48⟩)
    (hso : srci.toNat + 48 < 2 ^ 64) (hdo : dsti.toNat + 48 < 2 ^ 64)
    (hdisj : srci.toNat + 48 ≤ dsti.toNat ∨ dsti.toNat + 48 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((blsgLeToBeFn srci dsti inb ob).body.steps + 1)
      (0x8002f220 : Word) ret encCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** regOwns leScratch ** bytesRegion dsti ob ** bytesRegion srci inb)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
        ** bytesRegion dsti (blsgLeToBeBytes inb) ** bytesRegion srci inb) := by
  -- Surface the scratch registers at concrete (peeled) valuations.
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns leScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun vf => ?_))
  -- The adapter, at the packed register file.
  have had := Fn.retSpecFlat (blsgLeToBeFn srci dsti inb ob)
    (0x8002f220 : Word)
    (blsgLeToBeFn_spec srci dsti inb ob hwfR hwfW hilen (0x8002f220 : Word))
    (by show 4 * (18 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
    ob
    (by show ob.length = 48; exact holen)
    (by
      refine ⟨?_, ?_, rfl, holen, hilen, hso, hdo, hdisj, rfl⟩
      · show RegFile.get _ .x10 = srci
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
        exact if_pos rfl
      · show RegFile.get _ .x11 = dsti
        rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
        rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl)
    (fun _ _ _ h => h.2.2.2)
    (Q := regOwns exposedRegs ** bytesRegion dsti (blsgLeToBeBytes inb))
    (fun rf' ws' hlen' hpost' hp hh => by
      obtain ⟨hws', -, -, -⟩ := hpost'
      subst hws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  -- The adapter's CodeReq is exactly the callee's program; lift into `encCr`.
  rw [show (blsgLeToBeFn srci dsti inb ob).programRet (0x8002f220 : Word)
      = blsgLeToBe_prog from rfl] at had
  have hadC := liftCode (cr' := encCr) had (by code_mem)
  -- Reshape: project the region/rw fields, unpack the register file.
  rw [show (blsgLeToBeFn srci dsti inb ob).region = (⟨srci, inb⟩ : Region) from rfl,
      show (blsgLeToBeFn srci dsti inb ob).rw.base = dsti from rfl] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split2,
    show (if (Reg.x10 : Reg) = .x10 then srci else
        if (Reg.x10 : Reg) = .x11 then dsti else vf .x10) = srci from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then srci else
        if (Reg.x11 : Reg) = .x11 then dsti else vf .x11) = dsti from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then srci else if r = .x11 then dsti else vf r)
      vf leScratch
      (fun r hr => by
        show (if r = .x10 then srci else if r = .x11 then dsti else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_leScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_leScratch (hc ▸ hr))])]
    at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

-- ============================================================================
-- The per-iteration loop body (generic over `i < 4`).
-- ============================================================================

/-- The exposed registers the loop does not track between iterations. -/
def encRest : List Reg :=
  [.x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- One loop pass (`0x80033ed8 → 0x80033ef8`): compute the 48·i offset,
    point `a0`/`a1` at chunk `i`, CALL `blsg_le_to_be` (the adapter-derived
    contract), bump the counter, reload the bound. -/
private theorem encStep_spec (i : Nat) (hi : i < 4) (v1 : Word)
    (src dst : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 48) (holen : ob.length = 48)
    (hwfR : Region.wf ⟨src + BitVec.ofNat 64 (48 * i), inb⟩)
    (hwfW : RwRegion.wf ⟨dst + BitVec.ofNat 64 (48 * i), 48⟩)
    (hso : (src + BitVec.ofNat 64 (48 * i)).toNat + 48 < 2 ^ 64)
    (hdo : (dst + BitVec.ofNat 64 (48 * i)).toNat + 48 < 2 ^ 64)
    (hdisj : (src + BitVec.ofNat 64 (48 * i)).toNat + 48
          ≤ (dst + BitVec.ofNat 64 (48 * i)).toNat
        ∨ (dst + BitVec.ofNat 64 (48 * i)).toNat + 48
          ≤ (src + BitVec.ofNat 64 (48 * i)).toNat) :
    cpsTripleWithin ((blsgLeToBeFn 0 0 [] []).body.steps + 10)
      (0x80033ed8 : Word) (0x80033ef8 : Word) encCr
      ((.x18 ↦ᵣ BitVec.ofNat 64 i) ** regOwn .x5
        ** (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
          ** regOwn .x6 ** regOwn .x10 ** regOwn .x11 ** regOwns encRest
          ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
          ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb))
      ((.x18 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x5 ↦ᵣ BitVec.ofNat 64 4)
        ** (((.x1 : Reg) ↦ᵣ (0x80033ef0 : Word)) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
          ** regOwn .x6 ** regOwn .x10 ** regOwn .x11 ** regOwns encRest
          ** bytesRegion (dst + BitVec.ofNat 64 (48 * i))
              (blsgLeToBeBytes inb)
          ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)) := by
  -- Peel the four scratch registers the setup writes.
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns [.x5, .x6, .x10, .x11] (by decide)
      (P := (.x18 ↦ᵣ BitVec.ofNat 64 i) ** ((.x1 : Reg) ↦ᵣ v1)
        ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst) ** regOwns encRest
        ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
        ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
      (fun vf => ?_))
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  -- ---- the five setup instructions ----
  have hs1 := slli_spec_gen_within .x5 .x18 (vf .x5) (BitVec.ofNat 64 i)
    (4 : BitVec 6) (0x80033ed8 : Word) (by decide)
  rw [show ((4 : BitVec 6)).toNat = 4 from rfl,
      ofNat_shl i 4 16 (by norm_num) (by omega),
      show (0x80033ed8 : Word) + 4 = (0x80033edc : Word) from by decide] at hs1
  have hs1C := liftCode (cr' := encCr) hs1 (by code_mem)
  have hs2 := slli_spec_gen_within .x6 .x18 (vf .x6) (BitVec.ofNat 64 i)
    (5 : BitVec 6) (0x80033edc : Word) (by decide)
  rw [show ((5 : BitVec 6)).toNat = 5 from rfl,
      ofNat_shl i 5 32 (by norm_num) (by omega),
      show (0x80033edc : Word) + 4 = (0x80033ee0 : Word) from by decide] at hs2
  have hs2C := liftCode (cr' := encCr) hs2 (by code_mem)
  have hs3 := add_spec_gen_rd_eq_rs1_within .x5 .x6 (BitVec.ofNat 64 (16 * i))
    (BitVec.ofNat 64 (32 * i)) (0x80033ee0 : Word) (by decide)
  rw [show BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (32 * i)
        = BitVec.ofNat 64 (48 * i) from by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega,
      show (0x80033ee0 : Word) + 4 = (0x80033ee4 : Word) from by decide] at hs3
  have hs3C := liftCode (cr' := encCr) hs3 (by code_mem)
  have hs4 := add_spec_gen_within .x10 .x8 .x5 src (BitVec.ofNat 64 (48 * i))
    (vf .x10) (0x80033ee4 : Word) (by decide)
  rw [show (0x80033ee4 : Word) + 4 = (0x80033ee8 : Word) from by decide] at hs4
  have hs4C := liftCode (cr' := encCr) hs4 (by code_mem)
  have hs5 := add_spec_gen_within .x11 .x9 .x5 dst (BitVec.ofNat 64 (48 * i))
    (vf .x11) (0x80033ee8 : Word) (by decide)
  rw [show (0x80033ee8 : Word) + 4 = (0x80033eec : Word) from by decide] at hs5
  have hs5C := liftCode (cr' := encCr) hs5 (by code_mem)
  -- ---- the cross-call ----
  have hcallee := blsgLeToBeFlat_spec ((0x80033eec : Word) + 4)
    (src + BitVec.ofNat 64 (48 * i)) (dst + BitVec.ofNat 64 (48 * i)) inb ob
    hilen holen hwfR hwfW hso hdo hdisj (by decide)
  have hcall := callWithin_spec (0x80033eec : Word) (0x8002f220 : Word) v1
    (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg2_encode + 52))
    ((blsgLeToBeFn (src + BitVec.ofNat 64 (48 * i))
        (dst + BitVec.ofNat 64 (48 * i)) inb ob).body.steps + 1)
    (by decide) (by code_mem) (by pcf) hcallee
  rw [show (0x80033eec : Word) + 4 = (0x80033ef0 : Word) from by decide] at hcall
  -- hand the callee its scratch: `t0`/`t1` are concrete here, the rest owned
  have hcallW := cpsTripleWithin_weaken
    (P' := ((.x1 : Reg) ↦ᵣ v1) ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * i)))
      ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (48 * i)))
      ** (.x5 ↦ᵣ BitVec.ofNat 64 (48 * i)) ** (.x6 ↦ᵣ BitVec.ofNat 64 (32 * i))
      ** regOwns encRest
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (fun h hp => by
      simp only [leScratch, encRest, regOwns_cons, regOwns_nil,
        sepConj_emp_right'] at hp ⊢
      have hp1 : ((.x5 ↦ᵣ BitVec.ofNat 64 (48 * i))
          ** (.x6 ↦ᵣ BitVec.ofNat 64 (32 * i))
          ** (((.x1 : Reg) ↦ᵣ v1)
            ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * i)))
            ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (48 * i)))
            ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30
            ** regOwn .x31 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14
            ** regOwn .x15 ** regOwn .x16 ** regOwn .x17
            ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
            ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hp1
      xperm_hyp hp2)
    (fun _ hq => hq) hcall
  -- ---- counter bump and bound reload ----
  have ha := addi_spec_gen_same_within .x18 (BitVec.ofNat 64 i) (1 : BitVec 12)
    (0x80033ef0 : Word) (by decide)
  rw [cnt_step_up i (by omega),
      show (0x80033ef0 : Word) + 4 = (0x80033ef4 : Word) from by decide] at ha
  have haC := liftCode (cr' := encCr) ha (by code_mem)
  have hli := li_spec_gen_own_within .x5 (4 : Word) (0x80033ef4 : Word) (by decide)
  rw [show (0x80033ef4 : Word) + 4 = (0x80033ef8 : Word) from by decide,
      show (4 : Word) = BitVec.ofNat 64 4 from rfl] at hli
  have hliC := liftCode (cr' := encCr) hli (by code_mem)
  -- ---- frames + chain ----
  have hs1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** (.x6 ↦ᵣ vf .x6) ** (.x10 ↦ᵣ vf .x10)
      ** (.x11 ↦ᵣ vf .x11) ** regOwns encRest
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (by pcf) hs1C
  have hs2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** (.x5 ↦ᵣ BitVec.ofNat 64 (16 * i)) ** (.x10 ↦ᵣ vf .x10)
      ** (.x11 ↦ᵣ vf .x11) ** regOwns encRest
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (by pcf) hs2C
  have hs3F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 i) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11)
      ** regOwns encRest
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (by pcf) hs3C
  have hs4F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 i) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x9 ↦ᵣ dst)
      ** (.x6 ↦ᵣ BitVec.ofNat 64 (32 * i)) ** (.x11 ↦ᵣ vf .x11)
      ** regOwns encRest
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (by pcf) hs4C
  have hs5F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 i) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x6 ↦ᵣ BitVec.ofNat 64 (32 * i))
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * i))) ** regOwns encRest
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (by pcf) hs5C
  have hcallF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 i) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst))
    (by pcf) hcallW
  have haF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (0x80033ef0 : Word)) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
      ** regOwns exposedRegs
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) (blsgLeToBeBytes inb)
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (by pcf) haC
  have hliF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** ((.x1 : Reg) ↦ᵣ (0x80033ef0 : Word))
      ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
      ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11
      ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
      ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15
      ** regOwn .x16 ** regOwn .x17
      ** bytesRegion (dst + BitVec.ofNat 64 (48 * i)) (blsgLeToBeBytes inb)
      ** bytesRegion (src + BitVec.ofNat 64 (48 * i)) inb)
    (by pcf) hliC
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs1F hs2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hs3F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hs4F
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 hs5F
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 hcallF
  have c6 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [exposedRegs, regOwns_cons, regOwns_nil, sepConj_emp_right']
        at hp ⊢
      xperm_hyp hp) c5 haF
  have c7 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [exposedRegs, regOwns_cons, regOwns_nil, sepConj_emp_right']
        at hp
      xperm_hyp hp) c6 hliF
  rw [show (blsgLeToBeFn (src + BitVec.ofNat 64 (48 * i))
      (dst + BitVec.ofNat 64 (48 * i)) inb ob).body.steps
    = (blsgLeToBeFn 0 0 [] []).body.steps from rfl] at c7
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) c7)
  simp only [encRest, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hq ⊢
  xperm_hyp hq

-- ============================================================================
-- Chunk well-formedness from the global 192-byte facts.
-- ============================================================================

private theorem chunk_facts (b : Word) (n : Nat) (hn : n + 48 ≤ 192)
    (h8 : n % 8 = 0) (halign : b.toNat % 8 = 0) (hB : b.toNat + 192 < 2 ^ 64)
    (hv : ∀ k, k < 192 → isValidMemAddr (b + BitVec.ofNat 64 k) = true) :
    (b + BitVec.ofNat 64 n).toNat % 8 = 0
    ∧ (b + BitVec.ofNat 64 n).toNat + 48 < 2 ^ 64
    ∧ ∀ k, k < 48 →
        isValidMemAddr ((b + BitVec.ofNat 64 n) + BitVec.ofNat 64 k) = true := by
  have ht := toNat_add_ofNat b n (by omega)
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  rw [addr_fold]
  exact hv (n + k) (by omega)

-- ============================================================================
-- The loop invariant and the count-up loop.
-- ============================================================================

/-- Loop invariant at counter value `i`: the first `i` output chunks hold
    their big-endian encodings, the rest their original contents; the input
    chunks ride unchanged; `ra` holds the entry return address before the
    first call and the (constant) link address after any call. -/
def encInv (ret src dst : Word)
    (in0 in1 in2 in3 o0 o1 o2 o3 : List (BitVec 8)) (i : Nat) : Assertion :=
  (if i = 0 then ((.x1 : Reg) ↦ᵣ ret) else ((.x1 : Reg) ↦ᵣ (0x80033ef0 : Word)))
  ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
  ** regOwn .x6 ** regOwn .x10 ** regOwn .x11 ** regOwns encRest
  ** bytesRegion dst (if 0 < i then blsgLeToBeBytes in0 else o0)
  ** bytesRegion (dst + BitVec.ofNat 64 48) (if 1 < i then blsgLeToBeBytes in1 else o1)
  ** bytesRegion (dst + BitVec.ofNat 64 96) (if 2 < i then blsgLeToBeBytes in2 else o2)
  ** bytesRegion (dst + BitVec.ofNat 64 144) (if 3 < i then blsgLeToBeBytes in3 else o3)
  ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
  ** bytesRegion (src + BitVec.ofNat 64 96) in2
  ** bytesRegion (src + BitVec.ofNat 64 144) in3

private theorem pcFree_encInv (ret src dst : Word)
    (in0 in1 in2 in3 o0 o1 o2 o3 : List (BitVec 8)) (i : Nat) :
    (encInv ret src dst in0 in1 in2 in3 o0 o1 o2 o3 i).pcFree := by
  unfold encInv
  split_ifs <;> pcf

section Loop

variable (ret src dst : Word) (in0 in1 in2 in3 o0 o1 o2 o3 : List (BitVec 8))

/-- The per-iteration triple for `countupLoopBottom_spec`: case-split on the
    four concrete counter values, reduce the invariant's chunk selection,
    and frame `encStep_spec` with the untouched chunks. -/
private theorem encLoopBody_spec
    (hi0 : in0.length = 48) (hi1 : in1.length = 48) (hi2 : in2.length = 48)
    (hi3 : in3.length = 48)
    (ho0 : o0.length = 48) (ho1 : o1.length = 48) (ho2 : o2.length = 48)
    (ho3 : o3.length = 48)
    (halignS : src.toNat % 8 = 0) (halignD : dst.toNat % 8 = 0)
    (hsB : src.toNat + 192 < 2 ^ 64) (hdB : dst.toNat + 192 < 2 ^ 64)
    (hsv : ∀ k, k < 192 → isValidMemAddr (src + BitVec.ofNat 64 k) = true)
    (hdv : ∀ k, k < 192 → isValidMemAddr (dst + BitVec.ofNat 64 k) = true)
    (hdisj : src.toNat + 192 ≤ dst.toNat ∨ dst.toNat + 192 ≤ src.toNat)
    (i : Nat) (hi : i < 4) :
    cpsTripleWithin ((blsgLeToBeFn 0 0 [] []).body.steps + 10)
      (0x80033ed8 : Word) (0x80033ef8 : Word) encCr
      ((.x18 ↦ᵣ BitVec.ofNat 64 i) ** regOwn .x5
        ** encInv ret src dst in0 in1 in2 in3 o0 o1 o2 o3 i)
      ((.x18 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x5 ↦ᵣ BitVec.ofNat 64 4)
        ** encInv ret src dst in0 in1 in2 in3 o0 o1 o2 o3 (i + 1)) := by
  have hstep : ∀ (j : Nat), j < 4 → ∀ (v1 : Word) (inb ob : List (BitVec 8)),
      inb.length = 48 → ob.length = 48 →
      (48 * j) % 8 = 0 → 48 * j + 48 ≤ 192 →
      cpsTripleWithin ((blsgLeToBeFn 0 0 [] []).body.steps + 10)
        (0x80033ed8 : Word) (0x80033ef8 : Word) encCr
        ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** regOwn .x5
          ** (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
            ** regOwn .x6 ** regOwn .x10 ** regOwn .x11 ** regOwns encRest
            ** bytesRegion (dst + BitVec.ofNat 64 (48 * j)) ob
            ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb))
        ((.x18 ↦ᵣ BitVec.ofNat 64 (j + 1)) ** (.x5 ↦ᵣ BitVec.ofNat 64 4)
          ** (((.x1 : Reg) ↦ᵣ (0x80033ef0 : Word)) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
            ** regOwn .x6 ** regOwn .x10 ** regOwn .x11 ** regOwns encRest
            ** bytesRegion (dst + BitVec.ofNat 64 (48 * j)) (blsgLeToBeBytes inb)
            ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)) := by
    intro j hj v1 inb ob hinb hob h8 hle
    obtain ⟨hsA, hsO, hsV⟩ := chunk_facts src (48 * j) hle h8 halignS hsB hsv
    obtain ⟨hdA, hdO, hdV⟩ := chunk_facts dst (48 * j) hle h8 halignD hdB hdv
    have hts := toNat_add_ofNat src (48 * j) (by omega)
    have htd := toNat_add_ofNat dst (48 * j) (by omega)
    exact encStep_spec j hj v1 src dst inb ob hinb hob
      ⟨hsA, by simpa [hinb] using hsO, by
        intro k hk
        have hk48 : k < 48 := by simpa [hinb] using hk
        exact hsV k hk48⟩
      ⟨hdA, hdO, hdV⟩
      (by omega) (by omega)
      (by rw [hts, htd]; omega)
  interval_cases i
  · -- i = 0: chunk 0, entry `ra`.
    have h := hstep 0 (by omega) ret in0 o0 hi0 ho0 (by omega) (by omega)
    rw [show (48 * 0 : Nat) = 0 from rfl, add_ofNat_zero, add_ofNat_zero] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion (dst + BitVec.ofNat 64 48) o1
        ** bytesRegion (dst + BitVec.ofNat 64 96) o2
        ** bytesRegion (dst + BitVec.ofNat 64 144) o3
        ** bytesRegion (src + BitVec.ofNat 64 48) in1
        ** bytesRegion (src + BitVec.ofNat 64 96) in2
        ** bytesRegion (src + BitVec.ofNat 64 144) in3)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [encInv] at hp ⊢
      xperm_hyp hp
    · norm_num [encInv] at hq ⊢
      xperm_hyp hq
  · -- i = 1: chunk 1, link `ra`.
    have h := hstep 1 (by omega) (0x80033ef0 : Word) in1 o1 hi1 ho1
      (by omega) (by omega)
    rw [show (48 * 1 : Nat) = 48 from rfl] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion dst (blsgLeToBeBytes in0)
        ** bytesRegion (dst + BitVec.ofNat 64 96) o2
        ** bytesRegion (dst + BitVec.ofNat 64 144) o3
        ** bytesRegion src in0
        ** bytesRegion (src + BitVec.ofNat 64 96) in2
        ** bytesRegion (src + BitVec.ofNat 64 144) in3)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [encInv] at hp ⊢
      xperm_hyp hp
    · norm_num [encInv] at hq ⊢
      xperm_hyp hq
  · -- i = 2: chunk 2.
    have h := hstep 2 (by omega) (0x80033ef0 : Word) in2 o2 hi2 ho2
      (by omega) (by omega)
    rw [show (48 * 2 : Nat) = 96 from rfl] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion dst (blsgLeToBeBytes in0)
        ** bytesRegion (dst + BitVec.ofNat 64 48) (blsgLeToBeBytes in1)
        ** bytesRegion (dst + BitVec.ofNat 64 144) o3
        ** bytesRegion src in0
        ** bytesRegion (src + BitVec.ofNat 64 48) in1
        ** bytesRegion (src + BitVec.ofNat 64 144) in3)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [encInv] at hp ⊢
      xperm_hyp hp
    · norm_num [encInv] at hq ⊢
      xperm_hyp hq
  · -- i = 3: chunk 3.
    have h := hstep 3 (by omega) (0x80033ef0 : Word) in3 o3 hi3 ho3
      (by omega) (by omega)
    rw [show (48 * 3 : Nat) = 144 from rfl] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion dst (blsgLeToBeBytes in0)
        ** bytesRegion (dst + BitVec.ofNat 64 48) (blsgLeToBeBytes in1)
        ** bytesRegion (dst + BitVec.ofNat 64 96) (blsgLeToBeBytes in2)
        ** bytesRegion src in0
        ** bytesRegion (src + BitVec.ofNat 64 48) in1
        ** bytesRegion (src + BitVec.ofNat 64 96) in2)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [encInv] at hp ⊢
      xperm_hyp hp
    · norm_num [encInv] at hq ⊢
      xperm_hyp hq

end Loop

-- ============================================================================
-- The whole-routine ABI contract.
-- ============================================================================

/-- Entry values of the saved registers. -/
def encVals (ret arb8 arb9 arb18 : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ret | .x8 => arb8 | .x9 => arb9 | .x18 => arb18 | _ => 0

/-- Post-body values: `ra` holds the (fourth) call's link address, `s0`/`s1`
    the pointer copies, `s2` the exhausted counter. -/
def encVals' (src dst : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => (0x80033ef0 : Word) | .x8 => src | .x9 => dst
  | .x18 => BitVec.ofNat 64 4 | _ => 0

/-- **The whole-routine ABI contract for `blsg2_encode`.**  On return `sp`,
    `ra` (clobbered by FOUR real cross-calls), `s0`, `s1`, and the loop
    counter `s2` are restored to ENTRY values, and the 4 × 48-byte output
    record holds the big-endian encodings of the four input field elements
    (chunk `k` = `blsgLeToBeBytes in_k`) — the genuine, unweakened
    semantics — with the four input chunks untouched. -/
theorem blsg2Encode_spec (sp0 ret src dst arb8 arb9 arb18 : Word)
    (in0 in1 in2 in3 o0 o1 o2 o3 : List (BitVec 8))
    (hi0 : in0.length = 48) (hi1 : in1.length = 48) (hi2 : in2.length = 48)
    (hi3 : in3.length = 48)
    (ho0 : o0.length = 48) (ho1 : o1.length = 48) (ho2 : o2.length = 48)
    (ho3 : o3.length = 48)
    (halignS : src.toNat % 8 = 0) (halignD : dst.toNat % 8 = 0)
    (hsB : src.toNat + 192 < 2 ^ 64) (hdB : dst.toNat + 192 < 2 ^ 64)
    (hsv : ∀ k, k < 192 → isValidMemAddr (src + BitVec.ofNat 64 k) = true)
    (hdv : ∀ k, k < 192 → isValidMemAddr (dst + BitVec.ofNat 64 k) = true)
    (hdisj : src.toNat + 192 ≤ dst.toNat ∨ dst.toNat + 192 ≤ src.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + encFrame.length
        + (3 + 4 * ((blsgLeToBeFn 0 0 [] []).body.steps + 10 + 1))
        + encFrame.length + 1 + 1)
      (0x80033eb8 : Word) ret encCr
      ((.x2 ↦ᵣ sp0) ** regsAt encFrame (encVals ret arb8 arb9 arb18)
        ** frameSlotsOwn encFrame (sp0 + signExtend12 (-40 : BitVec 12))
        ** ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
          ** regOwn .x5 ** regOwn .x6 ** regOwns encRest
          ** bytesRegion dst o0 ** bytesRegion (dst + BitVec.ofNat 64 48) o1
          ** bytesRegion (dst + BitVec.ofNat 64 96) o2
          ** bytesRegion (dst + BitVec.ofNat 64 144) o3
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3))
      ((.x2 ↦ᵣ sp0) ** regsAt encFrame (encVals ret arb8 arb9 arb18)
        ** frameSlotsSaved encFrame (sp0 + signExtend12 (-40 : BitVec 12))
            (encVals ret arb8 arb9 arb18)
        ** (regOwn .x10 ** regOwn .x11
          ** regOwn .x5 ** regOwn .x6 ** regOwns encRest
          ** bytesRegion dst (blsgLeToBeBytes in0)
          ** bytesRegion (dst + BitVec.ofNat 64 48) (blsgLeToBeBytes in1)
          ** bytesRegion (dst + BitVec.ofNat 64 96) (blsgLeToBeBytes in2)
          ** bytesRegion (dst + BitVec.ofNat 64 144) (blsgLeToBeBytes in3)
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3)) := by
  -- ---- init: mv s0,a0 ; mv s1,a1 ; li s2,0 ----
  have hm1 := mv_spec_gen_within .x8 .x10 src arb8 (0x80033ecc : Word) (by decide)
  rw [show (0x80033ecc : Word) + 4 = (0x80033ed0 : Word) from by decide] at hm1
  have hm1C := liftCode (cr' := encCr) hm1 (by code_mem)
  have hm2 := mv_spec_gen_within .x9 .x11 dst arb9 (0x80033ed0 : Word) (by decide)
  rw [show (0x80033ed0 : Word) + 4 = (0x80033ed4 : Word) from by decide] at hm2
  have hm2C := liftCode (cr' := encCr) hm2 (by code_mem)
  have hm3 := li_spec_gen_within .x18 arb18 (0 : Word) (0x80033ed4 : Word) (by decide)
  rw [show (0x80033ed4 : Word) + 4 = (0x80033ed8 : Word) from by decide,
      show (0 : Word) = BitVec.ofNat 64 0 from rfl] at hm3
  have hm3C := liftCode (cr' := encCr) hm3 (by code_mem)
  -- ---- the count-up loop ----
  have hloop := countupLoopBottom_spec encCr (0x80033ed8 : Word) (0x80033ef8 : Word)
    .x18 .x5 (-32 : BitVec 13) ((blsgLeToBeFn 0 0 [] []).body.steps + 10) 4
    (encInv ret src dst in0 in1 in2 in3 o0 o1 o2 o3)
    (by omega) (by omega) (by decide)
    (fun n => pcFree_encInv ret src dst in0 in1 in2 in3 o0 o1 o2 o3 n)
    (by code_mem)
    (fun i hi => encLoopBody_spec ret src dst in0 in1 in2 in3 o0 o1 o2 o3
      hi0 hi1 hi2 hi3 ho0 ho1 ho2 ho3 halignS halignD hsB hdB hsv hdv hdisj i hi)
  rw [show (0x80033ef8 : Word) + 4 = (0x80033efc : Word) from by decide] at hloop
  -- ---- frames + chain into the single-exit body ----
  have STABLE := ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) ** regOwn .x5 ** regOwn .x6
    ** regOwns encRest
    ** bytesRegion dst o0 ** bytesRegion (dst + BitVec.ofNat 64 48) o1
    ** bytesRegion (dst + BitVec.ofNat 64 96) o2
    ** bytesRegion (dst + BitVec.ofNat 64 144) o3
    ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
    ** bytesRegion (src + BitVec.ofNat 64 96) in2
    ** bytesRegion (src + BitVec.ofNat 64 144) in3)
  have hm1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x9 ↦ᵣ arb9) ** (.x18 ↦ᵣ arb18)
      ** (.x11 ↦ᵣ dst) ** regOwn .x5 ** regOwn .x6 ** regOwns encRest
      ** bytesRegion dst o0 ** bytesRegion (dst + BitVec.ofNat 64 48) o1
      ** bytesRegion (dst + BitVec.ofNat 64 96) o2
      ** bytesRegion (dst + BitVec.ofNat 64 144) o3
      ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
      ** bytesRegion (src + BitVec.ofNat 64 96) in2
      ** bytesRegion (src + BitVec.ofNat 64 144) in3)
    (by pcf) hm1C
  have hm2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ src) ** (.x18 ↦ᵣ arb18)
      ** (.x10 ↦ᵣ src) ** regOwn .x5 ** regOwn .x6 ** regOwns encRest
      ** bytesRegion dst o0 ** bytesRegion (dst + BitVec.ofNat 64 48) o1
      ** bytesRegion (dst + BitVec.ofNat 64 96) o2
      ** bytesRegion (dst + BitVec.ofNat 64 144) o3
      ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
      ** bytesRegion (src + BitVec.ofNat 64 96) in2
      ** bytesRegion (src + BitVec.ofNat 64 144) in3)
    (by pcf) hm2C
  have hm3F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
      ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) ** regOwn .x5 ** regOwn .x6
      ** regOwns encRest
      ** bytesRegion dst o0 ** bytesRegion (dst + BitVec.ofNat 64 48) o1
      ** bytesRegion (dst + BitVec.ofNat 64 96) o2
      ** bytesRegion (dst + BitVec.ofNat 64 144) o3
      ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
      ** bytesRegion (src + BitVec.ofNat 64 96) in2
      ** bytesRegion (src + BitVec.ofNat 64 144) in3)
    (by pcf) hm3C
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hm1F hm2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hm3F
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      -- init post → loop pre: reduce the i = 0 invariant, release a0/a1.
      norm_num [encInv]
      have hp1 : ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
          ** ((.x18 ↦ᵣ BitVec.ofNat 64 0) ** regOwn .x5
            ** ((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
            ** regOwn .x6 ** regOwns encRest
            ** bytesRegion dst o0 ** bytesRegion (dst + BitVec.ofNat 64 48) o1
            ** bytesRegion (dst + BitVec.ofNat 64 96) o2
            ** bytesRegion (dst + BitVec.ofNat 64 144) o3
            ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
            ** bytesRegion (src + BitVec.ofNat 64 96) in2
            ** bytesRegion (src + BitVec.ofNat 64 144) in3)) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x10 src)
        (sepConj_mono (regIs_to_regOwn .x11 dst) (fun _ hh => hh)) h hp1
      xperm_hyp hp2)
    c2 hloop
  -- ---- the single-exit body triple, in `abiFrame_spec` shape ----
  have hbody : cpsTripleWithin
      (3 + 4 * ((blsgLeToBeFn 0 0 [] []).body.steps + 10 + 1))
      ((0x80033eb8 : Word) + BitVec.ofNat 64 (4 * (1 + encFrame.length)))
      ((0x80033eb8 : Word)
        + BitVec.ofNat 64 (4 * (1 + encFrame.length + encBody.length)))
      encCr
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-40 : BitVec 12)))
        ** regsAt encFrame (encVals ret arb8 arb9 arb18)
        ** frameSlotsSaved encFrame (sp0 + signExtend12 (-40 : BitVec 12))
            (encVals ret arb8 arb9 arb18)
        ** ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
          ** regOwn .x5 ** regOwn .x6 ** regOwns encRest
          ** bytesRegion dst o0 ** bytesRegion (dst + BitVec.ofNat 64 48) o1
          ** bytesRegion (dst + BitVec.ofNat 64 96) o2
          ** bytesRegion (dst + BitVec.ofNat 64 144) o3
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-40 : BitVec 12)))
        ** regsAt encFrame (encVals' src dst)
        ** frameSlotsSaved encFrame (sp0 + signExtend12 (-40 : BitVec 12))
            (encVals ret arb8 arb9 arb18)
        ** (regOwn .x10 ** regOwn .x11
          ** regOwn .x5 ** regOwn .x6 ** regOwns encRest
          ** bytesRegion dst (blsgLeToBeBytes in0)
          ** bytesRegion (dst + BitVec.ofNat 64 48) (blsgLeToBeBytes in1)
          ** bytesRegion (dst + BitVec.ofNat 64 96) (blsgLeToBeBytes in2)
          ** bytesRegion (dst + BitVec.ofNat 64 144) (blsgLeToBeBytes in3)
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3)) := by
    have hentry : (0x80033eb8 : Word) + BitVec.ofNat 64 (4 * (1 + encFrame.length))
        = (0x80033ecc : Word) := by decide
    have hexit : (0x80033eb8 : Word)
          + BitVec.ofNat 64 (4 * (1 + encFrame.length + encBody.length))
        = (0x80033efc : Word) := by decide
    rw [hentry, hexit]
    simp only [encFrame, regsAt, frameSlotsSaved, encVals, encVals',
      List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    have hchainF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-40 : BitVec 12)))
        ** (((sp0 + signExtend12 (-40 : BitVec 12))
              + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** (((sp0 + signExtend12 (-40 : BitVec 12))
              + signExtend12 (8 : BitVec 12)) ↦ₘ arb8)
        ** (((sp0 + signExtend12 (-40 : BitVec 12))
              + signExtend12 (16 : BitVec 12)) ↦ₘ arb9)
        ** (((sp0 + signExtend12 (-40 : BitVec 12))
              + signExtend12 (24 : BitVec 12)) ↦ₘ arb18))
      (by pcf) c3
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      hchainF
    norm_num [encInv] at hq ⊢
    have hq1 : (((.x5 : Reg) ↦ᵣ (4#64 : Word))
        ** ((.x18 ↦ᵣ (4#64 : Word)) ** ((.x1 : Reg) ↦ᵣ (2147696368 : Word))
          ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
          ** regOwn .x6 ** regOwn .x10 ** regOwn .x11 ** regOwns encRest
          ** bytesRegion dst (blsgLeToBeBytes in0)
          ** bytesRegion (dst + (48#64 : Word)) (blsgLeToBeBytes in1)
          ** bytesRegion (dst + (96#64 : Word)) (blsgLeToBeBytes in2)
          ** bytesRegion (dst + (144#64 : Word)) (blsgLeToBeBytes in3)
          ** bytesRegion src in0 ** bytesRegion (src + (48#64 : Word)) in1
          ** bytesRegion (src + (96#64 : Word)) in2
          ** bytesRegion (src + (144#64 : Word)) in3
          ** ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-40 : BitVec 12)))
          ** ((sp0 + signExtend12 (-40 : BitVec 12) + (0 : Word)) ↦ₘ ret)
          ** ((sp0 + signExtend12 (-40 : BitVec 12) + (8 : Word)) ↦ₘ arb8)
          ** ((sp0 + signExtend12 (-40 : BitVec 12) + (16 : Word)) ↦ₘ arb9)
          ** ((sp0 + signExtend12 (-40 : BitVec 12) + (24 : Word)) ↦ₘ arb18))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _) (fun _ hh => hh) h hq1
    xperm_hyp hq2
  abi_frame (40 : BitVec 12) halign hbody

#print axioms blsg2Encode_spec
#print axioms blsgLeToBeFlat_spec

end Bls12G2EncodeSAsm

end EvmAsm.Codegen
