/-
  EvmAsm.Codegen.Programs.Bls12KzgG2WireSAsm

  **The nested-loop-in-count-up port** (bead evm-asm-db2jq):
  `blsk_g2_wire`, byte-TRANSPARENT — the emitted `blskG2Wire_prog` IS an
  `abiFrameProg (-32)/(+32)` flatten with frame
  `[(ra,0),(s0,8),(s1,16),(s2,24)]` and a 27-instruction body:

      blsk_g2_wire:  addi sp, sp, -32 ; sd ra/s0/s1/s2
                     mv   s0, a0            -- src (4 × 48-byte LE elements)
                     mv   s1, a1            -- dst (4 × 64-byte wire records)
                     li   s2, 0             -- i := 0
             loop:   slli t0, s2, 6
                     add  t1, s1, t0        -- pad cursor = dst + 64·i
                     li   t2, 16
             pad:    sb   x0, 0(t1) ; addi t1, t1, 1
                     addi t2, t2, -1 ; bne t2, x0, pad   -- NESTED 16-byte pad
                     slli t0, s2, 4 ; slli t2, s2, 5
                     add  t0, t0, t2        -- 48·i
                     add  a0, s0, t0        -- src element i
                     slli t0, s2, 6
                     add  a1, s1, t0
                     addi a1, a1, 16        -- record body = dst + 64·i + 16
                     jal  ra, blsg_le_to_be -- encode element i
                     addi s2, s2, 1 ; li t0, 4 ; bne s2, t0, loop
                     ld … ; addi sp, sp, 32 ; ret

  The nested pad is one `zeroPadLoop_spec` (bead db2jq's reusable lemma)
  sequenced between the surrounding straight-line segments — exactly the
  nested-loop-in-count-up template documented in `ZeroPadLoop.lean`; the
  outer loop is `countupLoopBottom_spec` as in `Bls12G2EncodeSAsm`
  (#10057-family); the callee contract is DERIVED from
  `Bls12G1LeToBeSAsm.blsgLeToBeFn_spec` by `Fn.retSpecFlat`.

  **Genuine post** (`blskG2Wire_spec`): on return `sp`, `ra` (clobbered
  by four real `jal`s), `s0`, `s1`, `s2` are restored to ENTRY values,
  and each of the four 64-byte output records holds the 16-byte ZERO pad
  followed by the big-endian encoding of its input element
  (`pad_k = replicate 16 0`, `body_k = blsgLeToBeBytes in_k`) — with the
  four 48-byte input chunks untouched.
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.SAsm.ZeroPadLoop
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.Bls12Kzg
import EvmAsm.Codegen.Programs.Bls12G1LeToBeSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.SAsm.ZeroPadLoop (zeroPadLoop_spec)
open Bls12G1LeToBeSAsm (blsgLeToBeFn blsgLeToBeFn_spec blsgLeToBeBytes)

namespace Bls12KzgG2WireSAsm

-- ============================================================================
-- Anchors and byte-ties (semantic constants vs address anchors — guide §9).
-- ============================================================================

-- Semantic constants: 4 elements × (16-byte pad + 48-byte body) records.
-- Address anchors (`#guard`-tied to the live GuestAddrs):
#guard GuestAddrs.blsk_g2_wire = 0x80032e0c
#guard GuestAddrs.blsg_le_to_be = 0x8002f6b0

/-- The caller's 4-slot frame: `ra`, `s0`, `s1`, `s2`. -/
def wireFrame : FrameDesc := [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24)]

/-- The single-exit body: pointer copies, counter init, the count-up loop
    with the NESTED zero-pad countdown and the cross-call. -/
def wireBody : List Instr :=
  [ .MV .x8 .x10,
    .MV .x9 .x11,
    .LI .x18 (0 : Word),
    .SLLI .x5 .x18 (6 : BitVec 6),
    .ADD .x6 .x9 .x5,
    .LI .x7 (16 : Word),
    .SB .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .SLLI .x5 .x18 (4 : BitVec 6),
    .SLLI .x7 .x18 (5 : BitVec 6),
    .ADD .x5 .x5 .x7,
    .ADD .x10 .x8 .x5,
    .SLLI .x5 .x18 (6 : BitVec 6),
    .ADD .x11 .x9 .x5,
    .ADDI .x11 .x11 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsk_g2_wire + 88)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .LI .x5 (4 : Word),
    .BNE .x18 .x5 (-68 : BitVec 13) ]

-- Byte-transparency: the emitted routine IS the abiFrameProg flatten.
#guard abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) wireFrame wireBody
  = blskG2Wire_prog

/-- Byte-transparency, kernel-checked. -/
theorem wireProg_eq :
    abiFrameProg (-32 : BitVec 12) (32 : BitVec 12) wireFrame wireBody
      = blskG2Wire_prog := rfl

/-- The verification `CodeReq`: the caller at its guest address plus the
    callee at its guest address. -/
def wireCr : CodeReq :=
  (CodeReq.ofProg (GuestAddrs.blsk_g2_wire : Word) blskG2Wire_prog).union
    (CodeReq.ofProg (GuestAddrs.blsg_le_to_be : Word) blsgLeToBe_prog)

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

private theorem addi16_fold (p : Word) (m : Nat) :
    (p + BitVec.ofNat 64 m) + signExtend12 (16 : BitVec 12)
      = p + BitVec.ofNat 64 (m + 16) := by
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((16 : Word)).toNat = 16 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

-- ============================================================================
-- The callee's flat contract, derived by the adapter (`Fn.retSpecFlat`).
-- ============================================================================

/-- The exposed registers other than `a0`/`a1`. -/
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

/-- **The flat whole-routine contract for `blsg_le_to_be`** (at the LIVE
    guest addresses), derived from `blsgLeToBeFn_spec` by
    `Fn.retSpecFlat`, lifted into `wireCr`. -/
theorem blsgLeToBeWireFlat_spec (ret srci dsti : Word) (inb ob : List (BitVec 8))
    (hilen : inb.length = 48) (holen : ob.length = 48)
    (hwfR : Region.wf ⟨srci, inb⟩) (hwfW : RwRegion.wf ⟨dsti, 48⟩)
    (hso : srci.toNat + 48 < 2 ^ 64) (hdo : dsti.toNat + 48 < 2 ^ 64)
    (hdisj : srci.toNat + 48 ≤ dsti.toNat ∨ dsti.toNat + 48 ≤ srci.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((blsgLeToBeFn srci dsti inb ob).body.steps + 1)
      (GuestAddrs.blsg_le_to_be : Word) ret wireCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** regOwns leScratch ** bytesRegion dsti ob ** bytesRegion srci inb)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
        ** bytesRegion dsti (blsgLeToBeBytes inb) ** bytesRegion srci inb) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns leScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ srci) ** (.x11 ↦ᵣ dsti)
        ** bytesRegion dsti ob ** bytesRegion srci inb)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (blsgLeToBeFn srci dsti inb ob)
    (GuestAddrs.blsg_le_to_be : Word)
    (blsgLeToBeFn_spec srci dsti inb ob hwfR hwfW hilen (GuestAddrs.blsg_le_to_be : Word))
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
  rw [show (blsgLeToBeFn srci dsti inb ob).programRet (GuestAddrs.blsg_le_to_be : Word)
      = blsgLeToBe_prog from rfl] at had
  have hadC := liftCode (cr' := wireCr) had (by code_mem)
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
-- Sub-window well-formedness from the global 192/256-byte facts.
-- ============================================================================

private theorem sub_facts (b : Word) (n len tot : Nat) (hn : n + len ≤ tot)
    (h8 : n % 8 = 0) (halign : b.toNat % 8 = 0) (hB : b.toNat + tot < 2 ^ 64)
    (hv : ∀ k, k < tot → isValidMemAddr (b + BitVec.ofNat 64 k) = true) :
    (b + BitVec.ofNat 64 n).toNat % 8 = 0
    ∧ (b + BitVec.ofNat 64 n).toNat + len < 2 ^ 64
    ∧ ∀ k, k < len →
        isValidMemAddr ((b + BitVec.ofNat 64 n) + BitVec.ofNat 64 k) = true := by
  have ht := toNat_add_ofNat b n (by omega)
  refine ⟨by omega, by omega, fun k hk => ?_⟩
  rw [addr_fold]
  exact hv (n + k) (by omega)

-- ============================================================================
-- The per-iteration loop body (generic over `i < 4`).
-- ============================================================================

/-- The exposed registers the loop does not track between iterations. -/
def wireRest : List Reg :=
  [.x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

section Loop

variable (ret src dst : Word)
variable (in0 in1 in2 in3 : List (BitVec 8))
variable (p0 p1 p2 p3 o0 o1 o2 o3 : List (BitVec 8))

/-- Loop invariant at counter value `i`: the first `i` records are
    (zero pad, big-endian encoding); the rest hold their original
    contents; the input chunks ride unchanged. -/
def wireInv (i : Nat) : Assertion :=
  (if i = 0 then ((.x1 : Reg) ↦ᵣ ret) else ((.x1 : Reg) ↦ᵣ ((GuestAddrs.blsk_g2_wire : Word) + 92)))
  ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
  ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11
  ** regOwns wireRest
  ** bytesRegion dst
      (if 0 < i then List.replicate 16 (0 : BitVec 8) else p0)
  ** bytesRegion (dst + BitVec.ofNat 64 16)
      (if 0 < i then blsgLeToBeBytes in0 else o0)
  ** bytesRegion (dst + BitVec.ofNat 64 64)
      (if 1 < i then List.replicate 16 (0 : BitVec 8) else p1)
  ** bytesRegion (dst + BitVec.ofNat 64 80)
      (if 1 < i then blsgLeToBeBytes in1 else o1)
  ** bytesRegion (dst + BitVec.ofNat 64 128)
      (if 2 < i then List.replicate 16 (0 : BitVec 8) else p2)
  ** bytesRegion (dst + BitVec.ofNat 64 144)
      (if 2 < i then blsgLeToBeBytes in2 else o2)
  ** bytesRegion (dst + BitVec.ofNat 64 192)
      (if 3 < i then List.replicate 16 (0 : BitVec 8) else p3)
  ** bytesRegion (dst + BitVec.ofNat 64 208)
      (if 3 < i then blsgLeToBeBytes in3 else o3)
  ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
  ** bytesRegion (src + BitVec.ofNat 64 96) in2
  ** bytesRegion (src + BitVec.ofNat 64 144) in3

private theorem pcFree_wireInv (i : Nat) :
    (wireInv ret src dst in0 in1 in2 in3 p0 p1 p2 p3 o0 o1 o2 o3 i).pcFree := by
  unfold wireInv
  split_ifs <;> pcf

/-- One loop pass at chunk `j` (the body entry through body exit): pad-cursor
    setup, the NESTED 16-byte zero pad (`zeroPadLoop_spec`), the source /
    record-body address computation, the CALL, counter bump, bound
    reload. -/
private theorem wireStep_spec (j : Nat) (hj : j < 4) (v1 : Word)
    (inb pb ob : List (BitVec 8))
    (hilen : inb.length = 48) (hplen : pb.length = 16) (holen : ob.length = 48)
    (hwfR : Region.wf ⟨src + BitVec.ofNat 64 (48 * j), inb⟩)
    (hwfW : RwRegion.wf ⟨dst + BitVec.ofNat 64 (64 * j + 16), 48⟩)
    (hso : (src + BitVec.ofNat 64 (48 * j)).toNat + 48 < 2 ^ 64)
    (hdo : (dst + BitVec.ofNat 64 (64 * j + 16)).toNat + 48 < 2 ^ 64)
    (hdisj : (src + BitVec.ofNat 64 (48 * j)).toNat + 48
          ≤ (dst + BitVec.ofNat 64 (64 * j + 16)).toNat
        ∨ (dst + BitVec.ofNat 64 (64 * j + 16)).toNat + 48
          ≤ (src + BitVec.ofNat 64 (48 * j)).toNat)
    (halignP : (dst + BitVec.ofNat 64 (64 * j)).toNat % 8 = 0)
    (hpo : (dst + BitVec.ofNat 64 (64 * j)).toNat + 16 < 2 ^ 64)
    (hpv : ∀ k, k < 16 → isValidMemAddr
      ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin ((blsgLeToBeFn 0 0 [] []).body.steps + 79)
      ((GuestAddrs.blsk_g2_wire : Word) + 32) ((GuestAddrs.blsk_g2_wire : Word) + 100) wireCr
      ((.x18 ↦ᵣ BitVec.ofNat 64 j)
        ** (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
          ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** regOwn .x5 ** regOwn .x6 ** regOwn .x7
          ** regOwn .x10 ** regOwn .x11 ** regOwns wireRest
          ** bytesRegion (dst + BitVec.ofNat 64 (64 * j)) pb
          ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
          ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb))
      ((.x18 ↦ᵣ BitVec.ofNat 64 (j + 1)) ** (.x5 ↦ᵣ BitVec.ofNat 64 4)
        ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.blsk_g2_wire : Word) + 92)) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
          ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** regOwn .x6 ** regOwn .x7
          ** regOwn .x10 ** regOwn .x11 ** regOwns wireRest
          ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16))
              (blsgLeToBeBytes inb)
          ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)) := by
  -- Peel the five scratch registers the setup writes.
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns [.x5, .x6, .x7, .x10, .x11] (by decide)
      (P := (.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1)
        ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
        ** regOwns wireRest
        ** bytesRegion (dst + BitVec.ofNat 64 (64 * j)) pb
        ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
        ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
      (fun vf => ?_))
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  -- ---- pad-cursor setup: slli t0, s2, 6 ; add t1, s1, t0 ; li t2, 16 ----
  have hs1 := slli_spec_gen_within .x5 .x18 (vf .x5) (BitVec.ofNat 64 j)
    (6 : BitVec 6) ((GuestAddrs.blsk_g2_wire : Word) + 32) (by decide)
  rw [show ((6 : BitVec 6)).toNat = 6 from rfl,
      ofNat_shl j 6 64 (by norm_num) (by omega),
      show ((GuestAddrs.blsk_g2_wire : Word) + 32) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 36) from by decide] at hs1
  have hs1C := liftCode (cr' := wireCr) hs1 (by code_mem)
  have hs2 := add_spec_gen_within .x6 .x9 .x5 dst (BitVec.ofNat 64 (64 * j))
    (vf .x6) ((GuestAddrs.blsk_g2_wire : Word) + 36) (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 36) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 40) from by decide] at hs2
  have hs2C := liftCode (cr' := wireCr) hs2 (by code_mem)
  have hs3 := li_spec_gen_within .x7 (vf .x7) (16 : Word) ((GuestAddrs.blsk_g2_wire : Word) + 40)
    (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 40) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 44) from by decide,
      show (16 : Word) = BitVec.ofNat 64 16 from rfl] at hs3
  have hs3C := liftCode (cr' := wireCr) hs3 (by code_mem)
  -- ---- the NESTED 16-byte zero pad (the reusable lemma) ----
  have hpad := zeroPadLoop_spec wireCr ((GuestAddrs.blsk_g2_wire : Word) + 44) .x6 .x7
    (dst + BitVec.ofNat 64 (64 * j)) pb 16 (by decide) (by decide)
    (by omega) hplen halignP (by omega)
    (fun k hk => hpv k hk)
    (by code_mem) (by code_mem) (by code_mem) (by code_mem)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 44) + 16 = ((GuestAddrs.blsk_g2_wire : Word) + 60) from by decide] at hpad
  -- ---- source / record-body address computation ----
  have hs4 := slli_spec_gen_within .x5 .x18 (BitVec.ofNat 64 (64 * j))
    (BitVec.ofNat 64 j) (4 : BitVec 6) ((GuestAddrs.blsk_g2_wire : Word) + 60) (by decide)
  rw [show ((4 : BitVec 6)).toNat = 4 from rfl,
      ofNat_shl j 4 16 (by norm_num) (by omega),
      show ((GuestAddrs.blsk_g2_wire : Word) + 60) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 64) from by decide] at hs4
  have hs4C := liftCode (cr' := wireCr) hs4 (by code_mem)
  have hs5 := slli_spec_gen_within .x7 .x18 (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 j) (5 : BitVec 6) ((GuestAddrs.blsk_g2_wire : Word) + 64) (by decide)
  rw [show ((5 : BitVec 6)).toNat = 5 from rfl,
      ofNat_shl j 5 32 (by norm_num) (by omega),
      show ((GuestAddrs.blsk_g2_wire : Word) + 64) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 68) from by decide] at hs5
  have hs5C := liftCode (cr' := wireCr) hs5 (by code_mem)
  have hs6 := add_spec_gen_rd_eq_rs1_within .x5 .x7 (BitVec.ofNat 64 (16 * j))
    (BitVec.ofNat 64 (32 * j)) ((GuestAddrs.blsk_g2_wire : Word) + 68) (by decide)
  rw [show BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (32 * j)
        = BitVec.ofNat 64 (48 * j) from by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega,
      show ((GuestAddrs.blsk_g2_wire : Word) + 68) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 72) from by decide] at hs6
  have hs6C := liftCode (cr' := wireCr) hs6 (by code_mem)
  have hs7 := add_spec_gen_within .x10 .x8 .x5 src (BitVec.ofNat 64 (48 * j))
    (vf .x10) ((GuestAddrs.blsk_g2_wire : Word) + 72) (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 72) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 76) from by decide] at hs7
  have hs7C := liftCode (cr' := wireCr) hs7 (by code_mem)
  have hs8 := slli_spec_gen_within .x5 .x18 (BitVec.ofNat 64 (48 * j))
    (BitVec.ofNat 64 j) (6 : BitVec 6) ((GuestAddrs.blsk_g2_wire : Word) + 76) (by decide)
  rw [show ((6 : BitVec 6)).toNat = 6 from rfl,
      ofNat_shl j 6 64 (by norm_num) (by omega),
      show ((GuestAddrs.blsk_g2_wire : Word) + 76) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 80) from by decide] at hs8
  have hs8C := liftCode (cr' := wireCr) hs8 (by code_mem)
  have hs9 := add_spec_gen_within .x11 .x9 .x5 dst (BitVec.ofNat 64 (64 * j))
    (vf .x11) ((GuestAddrs.blsk_g2_wire : Word) + 80) (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 80) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 84) from by decide] at hs9
  have hs9C := liftCode (cr' := wireCr) hs9 (by code_mem)
  have hs10 := addi_spec_gen_same_within .x11 (dst + BitVec.ofNat 64 (64 * j))
    (16 : BitVec 12) ((GuestAddrs.blsk_g2_wire : Word) + 84) (by decide)
  rw [addi16_fold dst (64 * j),
      show ((GuestAddrs.blsk_g2_wire : Word) + 84) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 88) from by decide] at hs10
  have hs10C := liftCode (cr' := wireCr) hs10 (by code_mem)
  -- ---- the cross-call ----
  have hcallee := blsgLeToBeWireFlat_spec (((GuestAddrs.blsk_g2_wire : Word) + 88) + 4)
    (src + BitVec.ofNat 64 (48 * j)) (dst + BitVec.ofNat 64 (64 * j + 16))
    inb ob hilen holen hwfR hwfW hso hdo hdisj (by decide)
  have hcall := callWithin_spec ((GuestAddrs.blsk_g2_wire : Word) + 88) (GuestAddrs.blsg_le_to_be : Word) v1
    (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsk_g2_wire + 88))
    ((blsgLeToBeFn (src + BitVec.ofNat 64 (48 * j))
        (dst + BitVec.ofNat 64 (64 * j + 16)) inb ob).body.steps + 1)
    (by decide) (by code_mem) (by pcf) hcallee
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 88) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 92) from by decide] at hcall
  -- hand the callee its scratch: `t0`/`t1`/`t2` concrete, the rest owned
  have hcallW := cpsTripleWithin_weaken
    (P' := ((.x1 : Reg) ↦ᵣ v1) ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * j)))
      ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (64 * j + 16)))
      ** (.x5 ↦ᵣ BitVec.ofNat 64 (64 * j))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 (32 * j))
      ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (fun h hp => by
      simp only [leScratch, wireRest, regOwns_cons, regOwns_nil,
        sepConj_emp_right'] at hp ⊢
      have hp1 : ((.x5 ↦ᵣ BitVec.ofNat 64 (64 * j))
          ** ((.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
            ** ((.x7 ↦ᵣ BitVec.ofNat 64 (32 * j))
              ** (((.x1 : Reg) ↦ᵣ v1)
                ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * j)))
                ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (64 * j + 16)))
                ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
                ** regOwn .x12 ** regOwn .x13 ** regOwn .x14
                ** regOwn .x15 ** regOwn .x16 ** regOwn .x17
                ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
                ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)))) h := by
        xperm_hyp hp
      have hp2 := sepConj_mono (regIs_to_regOwn .x5 _)
        (sepConj_mono (regIs_to_regOwn .x6 _)
          (sepConj_mono (regIs_to_regOwn .x7 _) (fun _ hh => hh))) h hp1
      xperm_hyp hp2)
    (fun _ hq => hq) hcall
  -- ---- counter bump and bound reload ----
  have ha := addi_spec_gen_same_within .x18 (BitVec.ofNat 64 j) (1 : BitVec 12)
    ((GuestAddrs.blsk_g2_wire : Word) + 92) (by decide)
  rw [cnt_step_up j (by omega),
      show ((GuestAddrs.blsk_g2_wire : Word) + 92) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 96) from by decide] at ha
  have haC := liftCode (cr' := wireCr) ha (by code_mem)
  have hli := li_spec_gen_own_within .x5 (4 : Word) ((GuestAddrs.blsk_g2_wire : Word) + 96) (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 96) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 100) from by decide,
      show (4 : Word) = BitVec.ofNat 64 4 from rfl] at hli
  have hliC := liftCode (cr' := wireCr) hli (by code_mem)
  -- ---- frames + chain ----
  have hs1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x6 ↦ᵣ vf .x6) ** (.x7 ↦ᵣ vf .x7) ** (.x10 ↦ᵣ vf .x10)
      ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j)) pb
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs1C
  have hs2F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x7 ↦ᵣ vf .x7) ** (.x10 ↦ᵣ vf .x10)
      ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j)) pb
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs2C
  have hs3F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x5 ↦ᵣ BitVec.ofNat 64 (64 * j))
      ** (.x6 ↦ᵣ (dst + BitVec.ofNat 64 (64 * j)))
      ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j)) pb
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs3C
  have hpadF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** (.x5 ↦ᵣ BitVec.ofNat 64 (64 * j))
      ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hpad
  have hs4F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 0)
      ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs4C
  have hs5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x5 ↦ᵣ BitVec.ofNat 64 (16 * j))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs5C
  have hs6F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs6C
  have hs7F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 (32 * j))
      ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs7C
  have hs8F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 (32 * j))
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * j)))
      ** (.x11 ↦ᵣ vf .x11) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs8C
  have hs9F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 (32 * j))
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * j))) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs9C
  have hs10F := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** ((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src)
      ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** (.x5 ↦ᵣ BitVec.ofNat 64 (64 * j))
      ** (.x6 ↦ᵣ ((dst + BitVec.ofNat 64 (64 * j)) + BitVec.ofNat 64 16))
      ** (.x7 ↦ᵣ BitVec.ofNat 64 (32 * j))
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (48 * j))) ** regOwns wireRest
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hs10C
  have hcallF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 j) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
      ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8)))
    (by pcf) hcallW
  have haF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ((GuestAddrs.blsk_g2_wire : Word) + 92)) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
      ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16))
          (blsgLeToBeBytes inb)
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) haC
  have hliF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ BitVec.ofNat 64 (j + 1)) ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.blsk_g2_wire : Word) + 92))
      ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11
      ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
      ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 ** regOwn .x15
      ** regOwn .x16 ** regOwn .x17
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
          (List.replicate 16 (0 : BitVec 8))
      ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16))
          (blsgLeToBeBytes inb)
      ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)
    (by pcf) hliC
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hs1F hs2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hs3F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hpadF
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 hs4F
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 hs5F
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c5 hs6F
  have c7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c6 hs7F
  have c8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c7 hs8F
  have c9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c8 hs9F
  have c10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c9 hs10F
  have c11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c10 hcallF
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [exposedRegs, regOwns_cons, regOwns_nil, sepConj_emp_right']
        at hp ⊢
      xperm_hyp hp) c11 haF
  have c13 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [exposedRegs, regOwns_cons, regOwns_nil, sepConj_emp_right']
        at hp
      xperm_hyp hp) c12 hliF
  rw [show (blsgLeToBeFn (src + BitVec.ofNat 64 (48 * j))
      (dst + BitVec.ofNat 64 (64 * j + 16)) inb ob).body.steps
    = (blsgLeToBeFn 0 0 [] []).body.steps from rfl] at c13
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) c13)
  simp only [wireRest, regOwns_cons, regOwns_nil, sepConj_emp_right'] at hq ⊢
  xperm_hyp hq

/-- The per-iteration triple for `countupLoopBottom_spec`: case-split on
    the four counter values, reduce the invariant's record selection, and
    frame `wireStep_spec` with the untouched records. -/
private theorem wireLoopBody_spec
    (hi0 : in0.length = 48) (hi1 : in1.length = 48) (hi2 : in2.length = 48)
    (hi3 : in3.length = 48)
    (hp0 : p0.length = 16) (hp1 : p1.length = 16) (hp2 : p2.length = 16)
    (hp3 : p3.length = 16)
    (ho0 : o0.length = 48) (ho1 : o1.length = 48) (ho2 : o2.length = 48)
    (ho3 : o3.length = 48)
    (halignS : src.toNat % 8 = 0) (halignD : dst.toNat % 8 = 0)
    (hsB : src.toNat + 192 < 2 ^ 64) (hdB : dst.toNat + 256 < 2 ^ 64)
    (hsv : ∀ k, k < 192 → isValidMemAddr (src + BitVec.ofNat 64 k) = true)
    (hdv : ∀ k, k < 256 → isValidMemAddr (dst + BitVec.ofNat 64 k) = true)
    (hdisj : src.toNat + 192 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat)
    (i : Nat) (hi : i < 4) :
    cpsTripleWithin ((blsgLeToBeFn 0 0 [] []).body.steps + 79)
      ((GuestAddrs.blsk_g2_wire : Word) + 32) ((GuestAddrs.blsk_g2_wire : Word) + 100) wireCr
      ((.x18 ↦ᵣ BitVec.ofNat 64 i) ** regOwn .x5
        ** wireInv ret src dst in0 in1 in2 in3 p0 p1 p2 p3 o0 o1 o2 o3 i)
      ((.x18 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x5 ↦ᵣ BitVec.ofNat 64 4)
        ** wireInv ret src dst in0 in1 in2 in3 p0 p1 p2 p3 o0 o1 o2 o3 (i + 1))
    := by
  have hstep : ∀ (j : Nat), j < 4 → ∀ (v1 : Word) (inb pb ob : List (BitVec 8)),
      inb.length = 48 → pb.length = 16 → ob.length = 48 →
      (48 * j) % 8 = 0 → 48 * j + 48 ≤ 192 →
      (64 * j) % 8 = 0 → 64 * j + 64 ≤ 256 →
      cpsTripleWithin ((blsgLeToBeFn 0 0 [] []).body.steps + 79)
        ((GuestAddrs.blsk_g2_wire : Word) + 32) ((GuestAddrs.blsk_g2_wire : Word) + 100) wireCr
        ((.x18 ↦ᵣ BitVec.ofNat 64 j)
          ** (((.x1 : Reg) ↦ᵣ v1) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
            ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
            ** regOwn .x5 ** regOwn .x6 ** regOwn .x7
            ** regOwn .x10 ** regOwn .x11 ** regOwns wireRest
            ** bytesRegion (dst + BitVec.ofNat 64 (64 * j)) pb
            ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16)) ob
            ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb))
        ((.x18 ↦ᵣ BitVec.ofNat 64 (j + 1)) ** (.x5 ↦ᵣ BitVec.ofNat 64 4)
          ** (((.x1 : Reg) ↦ᵣ ((GuestAddrs.blsk_g2_wire : Word) + 92)) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
            ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
            ** regOwn .x6 ** regOwn .x7
            ** regOwn .x10 ** regOwn .x11 ** regOwns wireRest
            ** bytesRegion (dst + BitVec.ofNat 64 (64 * j))
                (List.replicate 16 (0 : BitVec 8))
            ** bytesRegion (dst + BitVec.ofNat 64 (64 * j + 16))
                (blsgLeToBeBytes inb)
            ** bytesRegion (src + BitVec.ofNat 64 (48 * j)) inb)) := by
    intro j hj v1 inb pb ob hinb hpb hob h848 hle48 h864 hle64
    obtain ⟨hsA, hsO, hsV⟩ := sub_facts src (48 * j) 48 192 hle48 h848
      halignS hsB hsv
    obtain ⟨hdA, hdO, hdV⟩ := sub_facts dst (64 * j + 16) 48 256
      (by omega) (by omega) halignD hdB hdv
    obtain ⟨hpA, hpO, hpV⟩ := sub_facts dst (64 * j) 16 256
      (by omega) h864 halignD hdB hdv
    have hts := toNat_add_ofNat src (48 * j) (by omega)
    have htd := toNat_add_ofNat dst (64 * j + 16) (by omega)
    exact wireStep_spec src dst j hj v1 inb pb ob hinb hpb hob
      ⟨hsA, by simpa [hinb] using hsO, by
        intro k hk
        have hk48 : k < 48 := by simpa [hinb] using hk
        exact hsV k hk48⟩
      ⟨hdA, hdO, hdV⟩
      (by omega) (by omega)
      (by rw [hts, htd]; rcases hdisj with h | h <;> omega)
      hpA hpO hpV
  interval_cases i
  · -- i = 0: record 0, entry `ra`.
    have h := hstep 0 (by omega) ret in0 p0 o0 hi0 hp0 ho0
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at h
    rw [add_ofNat_zero, add_ofNat_zero] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion (dst + BitVec.ofNat 64 64) p1
        ** bytesRegion (dst + BitVec.ofNat 64 80) o1
        ** bytesRegion (dst + BitVec.ofNat 64 128) p2
        ** bytesRegion (dst + BitVec.ofNat 64 144) o2
        ** bytesRegion (dst + BitVec.ofNat 64 192) p3
        ** bytesRegion (dst + BitVec.ofNat 64 208) o3
        ** bytesRegion (src + BitVec.ofNat 64 48) in1
        ** bytesRegion (src + BitVec.ofNat 64 96) in2
        ** bytesRegion (src + BitVec.ofNat 64 144) in3)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [wireInv] at hp ⊢
      xperm_hyp hp
    · norm_num [wireInv] at hq ⊢
      xperm_hyp hq
  · -- i = 1: record 1, link `ra`.
    have h := hstep 1 (by omega) ((GuestAddrs.blsk_g2_wire : Word) + 92) in1 p1 o1 hi1 hp1 ho1
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion dst (List.replicate 16 (0 : BitVec 8))
        ** bytesRegion (dst + BitVec.ofNat 64 16) (blsgLeToBeBytes in0)
        ** bytesRegion (dst + BitVec.ofNat 64 128) p2
        ** bytesRegion (dst + BitVec.ofNat 64 144) o2
        ** bytesRegion (dst + BitVec.ofNat 64 192) p3
        ** bytesRegion (dst + BitVec.ofNat 64 208) o3
        ** bytesRegion src in0
        ** bytesRegion (src + BitVec.ofNat 64 96) in2
        ** bytesRegion (src + BitVec.ofNat 64 144) in3)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [wireInv] at hp ⊢
      xperm_hyp hp
    · norm_num [wireInv] at hq ⊢
      xperm_hyp hq
  · -- i = 2: record 2.
    have h := hstep 2 (by omega) ((GuestAddrs.blsk_g2_wire : Word) + 92) in2 p2 o2 hi2 hp2 ho2
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion dst (List.replicate 16 (0 : BitVec 8))
        ** bytesRegion (dst + BitVec.ofNat 64 16) (blsgLeToBeBytes in0)
        ** bytesRegion (dst + BitVec.ofNat 64 64) (List.replicate 16 (0 : BitVec 8))
        ** bytesRegion (dst + BitVec.ofNat 64 80) (blsgLeToBeBytes in1)
        ** bytesRegion (dst + BitVec.ofNat 64 192) p3
        ** bytesRegion (dst + BitVec.ofNat 64 208) o3
        ** bytesRegion src in0
        ** bytesRegion (src + BitVec.ofNat 64 48) in1
        ** bytesRegion (src + BitVec.ofNat 64 144) in3)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [wireInv] at hp ⊢
      xperm_hyp hp
    · norm_num [wireInv] at hq ⊢
      xperm_hyp hq
  · -- i = 3: record 3.
    have h := hstep 3 (by omega) ((GuestAddrs.blsk_g2_wire : Word) + 92) in3 p3 o3 hi3 hp3 ho3
      (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at h
    have hF := cpsTripleWithin_frameR
      (bytesRegion dst (List.replicate 16 (0 : BitVec 8))
        ** bytesRegion (dst + BitVec.ofNat 64 16) (blsgLeToBeBytes in0)
        ** bytesRegion (dst + BitVec.ofNat 64 64) (List.replicate 16 (0 : BitVec 8))
        ** bytesRegion (dst + BitVec.ofNat 64 80) (blsgLeToBeBytes in1)
        ** bytesRegion (dst + BitVec.ofNat 64 128) (List.replicate 16 (0 : BitVec 8))
        ** bytesRegion (dst + BitVec.ofNat 64 144) (blsgLeToBeBytes in2)
        ** bytesRegion src in0
        ** bytesRegion (src + BitVec.ofNat 64 48) in1
        ** bytesRegion (src + BitVec.ofNat 64 96) in2)
      (by pcf) h
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · norm_num [wireInv] at hp ⊢
      xperm_hyp hp
    · norm_num [wireInv] at hq ⊢
      xperm_hyp hq

end Loop

-- ============================================================================
-- The whole-routine ABI contract.
-- ============================================================================

/-- Entry values of the saved registers. -/
def wireVals (ret arb8 arb9 arb18 : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ret | .x8 => arb8 | .x9 => arb9 | .x18 => arb18 | _ => 0

/-- Post-body values: `ra` holds the (fourth) call's link address, `s0`/`s1`
    the pointer copies, `s2` the exhausted counter. -/
def wireVals' (src dst : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ((GuestAddrs.blsk_g2_wire : Word) + 92) | .x8 => src | .x9 => dst
  | .x18 => BitVec.ofNat 64 4 | _ => 0

/-- **The whole-routine ABI contract for `blsk_g2_wire`.**  On return
    `sp`, `ra` (clobbered by FOUR real cross-calls), `s0`, `s1`, and the
    loop counter `s2` are restored to ENTRY values, and each of the four
    64-byte output records holds the 16-byte ZERO pad followed by the
    big-endian encoding of its input element — the genuine, unweakened
    semantics — with the four 48-byte input chunks untouched. -/
theorem blskG2Wire_spec (sp0 ret src dst arb8 arb9 arb18 : Word)
    (in0 in1 in2 in3 p0 p1 p2 p3 o0 o1 o2 o3 : List (BitVec 8))
    (hi0 : in0.length = 48) (hi1 : in1.length = 48) (hi2 : in2.length = 48)
    (hi3 : in3.length = 48)
    (hp0 : p0.length = 16) (hp1 : p1.length = 16) (hp2 : p2.length = 16)
    (hp3 : p3.length = 16)
    (ho0 : o0.length = 48) (ho1 : o1.length = 48) (ho2 : o2.length = 48)
    (ho3 : o3.length = 48)
    (halignS : src.toNat % 8 = 0) (halignD : dst.toNat % 8 = 0)
    (hsB : src.toNat + 192 < 2 ^ 64) (hdB : dst.toNat + 256 < 2 ^ 64)
    (hsv : ∀ k, k < 192 → isValidMemAddr (src + BitVec.ofNat 64 k) = true)
    (hdv : ∀ k, k < 256 → isValidMemAddr (dst + BitVec.ofNat 64 k) = true)
    (hdisj : src.toNat + 192 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + wireFrame.length
        + (3 + 4 * ((blsgLeToBeFn 0 0 [] []).body.steps + 79 + 1))
        + wireFrame.length + 1 + 1)
      (GuestAddrs.blsk_g2_wire : Word) ret wireCr
      ((.x2 ↦ᵣ sp0) ** regsAt wireFrame (wireVals ret arb8 arb9 arb18)
        ** frameSlotsOwn wireFrame (sp0 + signExtend12 (-32 : BitVec 12))
        ** ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
          ** bytesRegion dst p0 ** bytesRegion (dst + BitVec.ofNat 64 16) o0
          ** bytesRegion (dst + BitVec.ofNat 64 64) p1
          ** bytesRegion (dst + BitVec.ofNat 64 80) o1
          ** bytesRegion (dst + BitVec.ofNat 64 128) p2
          ** bytesRegion (dst + BitVec.ofNat 64 144) o2
          ** bytesRegion (dst + BitVec.ofNat 64 192) p3
          ** bytesRegion (dst + BitVec.ofNat 64 208) o3
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3))
      ((.x2 ↦ᵣ sp0) ** regsAt wireFrame (wireVals ret arb8 arb9 arb18)
        ** frameSlotsSaved wireFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (wireVals ret arb8 arb9 arb18)
        ** (regOwn .x10 ** regOwn .x11 ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
          ** bytesRegion dst (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 16) (blsgLeToBeBytes in0)
          ** bytesRegion (dst + BitVec.ofNat 64 64)
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 80) (blsgLeToBeBytes in1)
          ** bytesRegion (dst + BitVec.ofNat 64 128)
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 144) (blsgLeToBeBytes in2)
          ** bytesRegion (dst + BitVec.ofNat 64 192)
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 208) (blsgLeToBeBytes in3)
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3)) := by
  -- ---- init: mv s0,a0 ; mv s1,a1 ; li s2,0 ----
  have hm1 := mv_spec_gen_within .x8 .x10 src arb8 ((GuestAddrs.blsk_g2_wire : Word) + 20) (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 20) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 24) from by decide] at hm1
  have hm1C := liftCode (cr' := wireCr) hm1 (by code_mem)
  have hm2 := mv_spec_gen_within .x9 .x11 dst arb9 ((GuestAddrs.blsk_g2_wire : Word) + 24) (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 24) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 28) from by decide] at hm2
  have hm2C := liftCode (cr' := wireCr) hm2 (by code_mem)
  have hm3 := li_spec_gen_within .x18 arb18 (0 : Word) ((GuestAddrs.blsk_g2_wire : Word) + 28) (by decide)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 28) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 32) from by decide,
      show (0 : Word) = BitVec.ofNat 64 0 from rfl] at hm3
  have hm3C := liftCode (cr' := wireCr) hm3 (by code_mem)
  -- ---- the count-up loop ----
  have hloop := countupLoopBottom_spec wireCr ((GuestAddrs.blsk_g2_wire : Word) + 32) ((GuestAddrs.blsk_g2_wire : Word) + 100)
    .x18 .x5 (-68 : BitVec 13) ((blsgLeToBeFn 0 0 [] []).body.steps + 79) 4
    (wireInv ret src dst in0 in1 in2 in3 p0 p1 p2 p3 o0 o1 o2 o3)
    (by omega) (by omega) (by decide)
    (fun n => pcFree_wireInv ret src dst in0 in1 in2 in3 p0 p1 p2 p3 o0 o1 o2 o3 n)
    (by code_mem)
    (fun i hi => wireLoopBody_spec ret src dst in0 in1 in2 in3 p0 p1 p2 p3
      o0 o1 o2 o3 hi0 hi1 hi2 hi3 hp0 hp1 hp2 hp3 ho0 ho1 ho2 ho3
      halignS halignD hsB hdB hsv hdv hdisj i hi)
  rw [show ((GuestAddrs.blsk_g2_wire : Word) + 100) + 4 = ((GuestAddrs.blsk_g2_wire : Word) + 104) from by decide] at hloop
  -- ---- frames + chain into the single-exit body ----
  have hm1F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x9 ↦ᵣ arb9) ** (.x18 ↦ᵣ arb18)
      ** (.x11 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
      ** bytesRegion dst p0 ** bytesRegion (dst + BitVec.ofNat 64 16) o0
      ** bytesRegion (dst + BitVec.ofNat 64 64) p1
      ** bytesRegion (dst + BitVec.ofNat 64 80) o1
      ** bytesRegion (dst + BitVec.ofNat 64 128) p2
      ** bytesRegion (dst + BitVec.ofNat 64 144) o2
      ** bytesRegion (dst + BitVec.ofNat 64 192) p3
      ** bytesRegion (dst + BitVec.ofNat 64 208) o3
      ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
      ** bytesRegion (src + BitVec.ofNat 64 96) in2
      ** bytesRegion (src + BitVec.ofNat 64 144) in3)
    (by pcf) hm1C
  have hm2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ src) ** (.x18 ↦ᵣ arb18)
      ** (.x10 ↦ᵣ src) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
      ** bytesRegion dst p0 ** bytesRegion (dst + BitVec.ofNat 64 16) o0
      ** bytesRegion (dst + BitVec.ofNat 64 64) p1
      ** bytesRegion (dst + BitVec.ofNat 64 80) o1
      ** bytesRegion (dst + BitVec.ofNat 64 128) p2
      ** bytesRegion (dst + BitVec.ofNat 64 144) o2
      ** bytesRegion (dst + BitVec.ofNat 64 192) p3
      ** bytesRegion (dst + BitVec.ofNat 64 208) o3
      ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
      ** bytesRegion (src + BitVec.ofNat 64 96) in2
      ** bytesRegion (src + BitVec.ofNat 64 144) in3)
    (by pcf) hm2C
  have hm3F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
      ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
      ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
      ** bytesRegion dst p0 ** bytesRegion (dst + BitVec.ofNat 64 16) o0
      ** bytesRegion (dst + BitVec.ofNat 64 64) p1
      ** bytesRegion (dst + BitVec.ofNat 64 80) o1
      ** bytesRegion (dst + BitVec.ofNat 64 128) p2
      ** bytesRegion (dst + BitVec.ofNat 64 144) o2
      ** bytesRegion (dst + BitVec.ofNat 64 192) p3
      ** bytesRegion (dst + BitVec.ofNat 64 208) o3
      ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
      ** bytesRegion (src + BitVec.ofNat 64 96) in2
      ** bytesRegion (src + BitVec.ofNat 64 144) in3)
    (by pcf) hm3C
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hm1F hm2F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hm3F
  have c3 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      norm_num [wireInv]
      have hp1 : ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
          ** ((.x18 ↦ᵣ BitVec.ofNat 64 0) ** regOwn .x5
            ** ((.x1 : Reg) ↦ᵣ ret) ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst)
            ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
            ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
            ** bytesRegion dst p0 ** bytesRegion (dst + BitVec.ofNat 64 16) o0
            ** bytesRegion (dst + BitVec.ofNat 64 64) p1
            ** bytesRegion (dst + BitVec.ofNat 64 80) o1
            ** bytesRegion (dst + BitVec.ofNat 64 128) p2
            ** bytesRegion (dst + BitVec.ofNat 64 144) o2
            ** bytesRegion (dst + BitVec.ofNat 64 192) p3
            ** bytesRegion (dst + BitVec.ofNat 64 208) o3
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
      (3 + 4 * ((blsgLeToBeFn 0 0 [] []).body.steps + 79 + 1))
      ((GuestAddrs.blsk_g2_wire : Word) + BitVec.ofNat 64 (4 * (1 + wireFrame.length)))
      ((GuestAddrs.blsk_g2_wire : Word)
        + BitVec.ofNat 64 (4 * (1 + wireFrame.length + wireBody.length)))
      wireCr
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
        ** regsAt wireFrame (wireVals ret arb8 arb9 arb18)
        ** frameSlotsSaved wireFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (wireVals ret arb8 arb9 arb18)
        ** ((.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
          ** bytesRegion dst p0 ** bytesRegion (dst + BitVec.ofNat 64 16) o0
          ** bytesRegion (dst + BitVec.ofNat 64 64) p1
          ** bytesRegion (dst + BitVec.ofNat 64 80) o1
          ** bytesRegion (dst + BitVec.ofNat 64 128) p2
          ** bytesRegion (dst + BitVec.ofNat 64 144) o2
          ** bytesRegion (dst + BitVec.ofNat 64 192) p3
          ** bytesRegion (dst + BitVec.ofNat 64 208) o3
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
        ** regsAt wireFrame (wireVals' src dst)
        ** frameSlotsSaved wireFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (wireVals ret arb8 arb9 arb18)
        ** (regOwn .x10 ** regOwn .x11 ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwns wireRest
          ** bytesRegion dst (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 16) (blsgLeToBeBytes in0)
          ** bytesRegion (dst + BitVec.ofNat 64 64)
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 80) (blsgLeToBeBytes in1)
          ** bytesRegion (dst + BitVec.ofNat 64 128)
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 144) (blsgLeToBeBytes in2)
          ** bytesRegion (dst + BitVec.ofNat 64 192)
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + BitVec.ofNat 64 208) (blsgLeToBeBytes in3)
          ** bytesRegion src in0 ** bytesRegion (src + BitVec.ofNat 64 48) in1
          ** bytesRegion (src + BitVec.ofNat 64 96) in2
          ** bytesRegion (src + BitVec.ofNat 64 144) in3)) := by
    have hentry : (GuestAddrs.blsk_g2_wire : Word) + BitVec.ofNat 64 (4 * (1 + wireFrame.length))
        = ((GuestAddrs.blsk_g2_wire : Word) + 20) := by decide
    have hexit : (GuestAddrs.blsk_g2_wire : Word)
          + BitVec.ofNat 64 (4 * (1 + wireFrame.length + wireBody.length))
        = ((GuestAddrs.blsk_g2_wire : Word) + 104) := by decide
    rw [hentry, hexit]
    simp only [wireFrame, regsAt, frameSlotsSaved, wireVals, wireVals',
      List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    have hchainF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
        ** (((sp0 + signExtend12 (-32 : BitVec 12))
              + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** (((sp0 + signExtend12 (-32 : BitVec 12))
              + signExtend12 (8 : BitVec 12)) ↦ₘ arb8)
        ** (((sp0 + signExtend12 (-32 : BitVec 12))
              + signExtend12 (16 : BitVec 12)) ↦ₘ arb9)
        ** (((sp0 + signExtend12 (-32 : BitVec 12))
              + signExtend12 (24 : BitVec 12)) ↦ₘ arb18))
      (by pcf) c3
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      hchainF
    norm_num [wireInv, GuestAddrs.blsk_g2_wire] at hq ⊢
    have hq1 : (((.x5 : Reg) ↦ᵣ (4#64 : Word))
        ** ((.x18 ↦ᵣ (4#64 : Word)) ** ((.x1 : Reg) ↦ᵣ ((GuestAddrs.blsk_g2_wire : Word) + 92))
          ** (.x8 ↦ᵣ src) ** (.x9 ↦ᵣ dst) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11
          ** regOwns wireRest
          ** bytesRegion dst (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + (16#64 : Word)) (blsgLeToBeBytes in0)
          ** bytesRegion (dst + (64#64 : Word))
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + (80#64 : Word)) (blsgLeToBeBytes in1)
          ** bytesRegion (dst + (128#64 : Word))
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + (144#64 : Word)) (blsgLeToBeBytes in2)
          ** bytesRegion (dst + (192#64 : Word))
              (List.replicate 16 (0 : BitVec 8))
          ** bytesRegion (dst + (208#64 : Word)) (blsgLeToBeBytes in3)
          ** bytesRegion src in0 ** bytesRegion (src + (48#64 : Word)) in1
          ** bytesRegion (src + (96#64 : Word)) in2
          ** bytesRegion (src + (144#64 : Word)) in3
          ** ((.x2 : Reg) ↦ᵣ (sp0 + signExtend12 (-32 : BitVec 12)))
          ** ((sp0 + signExtend12 (-32 : BitVec 12) + (0 : Word)) ↦ₘ ret)
          ** ((sp0 + signExtend12 (-32 : BitVec 12) + (8 : Word)) ↦ₘ arb8)
          ** ((sp0 + signExtend12 (-32 : BitVec 12) + (16 : Word)) ↦ₘ arb9)
          ** ((sp0 + signExtend12 (-32 : BitVec 12) + (24 : Word)) ↦ₘ arb18))) h := by
      norm_num [GuestAddrs.blsk_g2_wire] at hq ⊢
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _) (fun _ hh => hh) h hq1
    norm_num [GuestAddrs.blsk_g2_wire] at hq2 ⊢
    xperm_hyp hq2
  abi_frame (32 : BitVec 12) halign hbody

#print axioms blskG2Wire_spec
#print axioms blsgLeToBeWireFlat_spec

end Bls12KzgG2WireSAsm

end EvmAsm.Codegen
