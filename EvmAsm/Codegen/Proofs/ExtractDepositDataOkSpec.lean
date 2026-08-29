/-
  EvmAsm.Codegen.Proofs.ExtractDepositDataOkSpec

  Second tranche of #12989: the ok path of `extract_deposit_data` at its
  linked guest address, as a flat whole-path `cpsTripleWithin` over the
  shared three-entry bundle image `extractDepositDataBundle_prog`.  A
  576-byte DepositEvent payload whose ten ABI header fields all pass the
  `edd_be32_eq` checks has its five raw fields copied to the 192-byte
  output arena by `edd_memcpy` and the routine returns `a0 = 0` with
  `sp`/`ra`/`s0`/`s1` restored.

  The composition: the frame prologue and the not-taken length guard
  (as in the fail arm), then ten `jal ra, edd_be32_eq` call groups and
  five `jal ra, edd_memcpy` call groups, each composed by
  `callWithin_spec` with the leaves' DCode `retSpec`s — packing the
  caller's exposed-register atoms into the callee's `asrtM` register
  file and unpacking on return.  `sp`/`s0`/`s1`/`ra` are NOT in
  `exposedRegs`, so they are framed (never handed to a callee); the
  five `edd_memcpy` call-site premises are the #12805 discharges.
-/

import EvmAsm.Codegen.Programs.ExtractDepositData
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.ExtractDepositDataOkSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen (extractDepositData_prog extractDepositDataBundle_prog
  eddDataPtr eddOutPtr EddMemcpyCallSite)

/-- The routine's guest entry. -/
abbrev EddB : Word := (GuestAddrs.extract_deposit_data : Word)

/-- The shared three-entry bundle image at the guest entry:
    main body (76 insns) ++ `edd_be32_eq` (23) ++ `edd_memcpy` (8). -/
abbrev eddbCode : CodeReq :=
  CodeReq.ofProg EddB extractDepositDataBundle_prog

private theorem eddbProg_len :
    (extractDepositDataBundle_prog : List Instr).length = 107 := by decide

/-- Membership of the `k`-th bundle instruction's singleton in the
    bundle image. -/
private theorem eddb_mem (k : Nat) (ins : Instr) (A : Word)
    (hA : A = EddB + BitVec.ofNat 64 (4 * k))
    (hk : k < 107)
    (hins : (extractDepositDataBundle_prog : List Instr)[k]'(by
      rw [eddbProg_len]; omega) = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → eddbCode a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at EddB A extractDepositDataBundle_prog k ins hA
      (by rw [eddbProg_len]; omega) hins
      (by rw [eddbProg_len]; norm_num) a i h

/-! ## The leaves inside the bundle

    `edd_be32_eq` occupies instruction indices 76..98 (entry
    `EddB + 304`), `edd_memcpy` indices 99..106 (entry `EddB + 396`). -/

/-- The `edd_be32_eq` derivation's generated `Stmt`, pinned explicitly:
    the ghost arguments survive only in the loop-invariant slot, which
    `flatten`/`steps` ignore — pinning the shape lets the kernel reduce
    them without recursing through the derivation's proof fields. -/
private theorem eddDeriv_stmt (ptr : Word) (bs : List (BitVec 8)) (K : Word) :
    (EddBe32EqSAsm.eddDeriv ptr bs K).stmt
      = Stmt.seq (.block "init" [.LI .x5 (0 : Word)])
          (.retWhileHeaderBreak "zscan" (.block "hdr" [.LI .x6 (28 : Word)])
            (.bne .x5 .x6) 28
            (fun i rf ws A => EddBe32EqSAsm.eddInv ptr bs K i rf ws A)
            (.block "byte" [.ADD .x7 .x10 .x5, .LBU .x28 .x7 (0 : BitVec 12)])
            (.bne .x28 .x0)
            (.block "bump" [.ADDI .x5 .x5 (1 : BitVec 12)])
            [(EddBe32EqSAsm.eddStage, .bne .x6 .x11)]
            (.seq (.block "eq" [.LI .x10 (1 : Word)]) (.retJalr "eqr"))
            (.seq (.block "ne" [.LI .x10 (0 : Word)]) (.retJalr "ner"))) := rfl

set_option maxRecDepth 100000 in
/-- `eddDeriv`'s flatten is ghost-independent and position-independent:
    the pinned program at any base. -/
private theorem be32_flatten (ptr : Word) (bs : List (BitVec 8)) (K : Word)
    (b : Word) :
    ((EddBe32EqSAsm.eddDeriv ptr bs K).stmt.flatten b : List Instr)
      = EddBe32EqSAsm.eddBe32Eq_prog := by
  rw [eddDeriv_stmt]; rfl

set_option maxRecDepth 100000 in
private theorem be32_steps (ptr : Word) (bs : List (BitVec 8)) (K : Word) :
    (EddBe32EqSAsm.eddDeriv ptr bs K).stmt.steps = 632 := by
  rw [eddDeriv_stmt]; rfl

set_option maxRecDepth 100000 in
/-- The `edd_memcpy` leaf flattened at its bundle address is the pinned
    program (its flatten is ghost-independent by
    `mcDeriv_flatten_ghost_free`). -/
private theorem mc_flatten_at :
    ((EddMemcpySAsm.mcDeriv 0 0 [] [] 0).stmt.flatten (EddB + 396) : List Instr)
      = EddMemcpySAsm.eddMemcpy_prog := by decide

set_option maxRecDepth 100000 in
private theorem mc_steps_ghost_free (s d : Word) (bs ws : List (BitVec 8))
    (n : Nat) :
    (EddMemcpySAsm.mcDeriv s d bs ws n).stmt.steps
      = (EddMemcpySAsm.mcDeriv 0 0 [] [] n).stmt.steps := rfl

set_option maxRecDepth 100000 in
private theorem mc_steps_48 :
    (EddMemcpySAsm.mcDeriv 0 0 [] [] 48).stmt.steps = 338 := by decide
set_option maxRecDepth 100000 in
private theorem mc_steps_32 :
    (EddMemcpySAsm.mcDeriv 0 0 [] [] 32).stmt.steps = 226 := by decide
set_option maxRecDepth 100000 in
private theorem mc_steps_8 :
    (EddMemcpySAsm.mcDeriv 0 0 [] [] 8).stmt.steps = 58 := by decide
set_option maxRecDepth 100000 in
private theorem mc_steps_96 :
    (EddMemcpySAsm.mcDeriv 0 0 [] [] 96).stmt.steps = 674 := by decide

set_option maxRecDepth 20000 in
/-- The `edd_be32_eq` program is the bundle's slice at index 76. -/
private theorem be32_sub :
    ∀ a i, CodeReq.ofProg (EddB + 304)
        (EddBe32EqSAsm.eddBe32Eq_prog : List Instr) a = some i →
      eddbCode a = some i :=
  CodeReq.ofProg_mono_sub EddB (EddB + 304)
    extractDepositDataBundle_prog EddBe32EqSAsm.eddBe32Eq_prog 76
    (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 20000 in
/-- The `edd_memcpy` program is the bundle's slice at index 99. -/
private theorem mc_sub :
    ∀ a i, CodeReq.ofProg (EddB + 396)
        (EddMemcpySAsm.eddMemcpy_prog : List Instr) a = some i →
      eddbCode a = some i :=
  CodeReq.ofProg_mono_sub EddB (EddB + 396)
    extractDepositDataBundle_prog EddMemcpySAsm.eddMemcpy_prog 99
    (by decide) (by decide) (by decide) (by decide)

/-- `pcFree` discharge extended with the region/ownership atoms this
    file frames. -/
local macro "edd_pcfree" : tactic => `(tactic| repeat (first
  | apply pcFree_sepConj
  | exact pcFree_regIs
  | exact pcFree_regOwn
  | exact pcFree_memIs
  | exact pcFree_emp
  | exact pcFree_pure
  | exact bytesRegion_pcFree _ _
  | exact pcFree_regAtomsOf _ _
  | exact pcFree_regOwns _
  | exact pcFree_asrtM _ _ _))

/-! ## Exposed-register bookkeeping -/

/-- The exposed registers except `a0` — what a call group returns to
    ownership after reading the callee's `a0`. -/
def eddScr14 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The exposed registers except `a0`/`a1` — the untouched rest during a
    check group's argument setup. -/
def eddScr13 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

/-- The exposed registers except `a0`/`a1`/`a2` — the untouched rest
    during a copy group's argument setup. -/
def eddScr12 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem edd_split_pre2 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x10 : Reg) ↦ᵣ vf .x10) ** ((.x11 : Reg) ↦ᵣ vf .x11) **
          regAtomsOf vf eddScr13) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [eddScr13, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem edd_split_pre3 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x10 : Reg) ↦ᵣ vf .x10) ** ((.x11 : Reg) ↦ᵣ vf .x11) **
          ((.x12 : Reg) ↦ᵣ vf .x12) ** regAtomsOf vf eddScr12) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [eddScr12, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem edd_split_post (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x10 : Reg) ↦ᵣ vf .x10) ** regAtomsOf vf eddScr14) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [eddScr14, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- `regOwn a0` plus the other fourteen recombine into the whole exposed
    ownership. -/
private theorem edd_owns_recombine :
    ∀ h, (regOwn .x10 ** regOwns eddScr14) h → regOwns exposedRegs h := by
  intro h hp
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] h
  simp only [regOwns_cons, regOwns_nil]
  simp only [eddScr14, regOwns_cons, regOwns_nil] at hp
  xperm_hyp hp

/-! ## Packing the caller's atoms into the callee's `asrtM` -/

/-- The explicit callee-entry register file for a check call. -/
private def be32Rf (ptr K : Word) (vf : Reg → Word) : RegFile :=
  fun r => if r = .x10 then ptr else if r = .x11 then K else vf r

/-- Pack: the caller's fifteen exposed atoms (with `a0 = ptr`,
    `a1 = K`) plus the field bytes satisfy `edd_be32_eq`'s
    precondition. -/
private theorem edd_pack_be32 (ptr K : Word) (bsC : List (BitVec 8))
    (vf : Reg → Word) (hlen : 32 ≤ bsC.length) :
    ∀ h, ((((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ K) **
        regAtomsOf vf eddScr13) ** bytesRegion ptr bsC) h →
      asrtM ⟨ptr, bsC⟩ RwRegion.empty
        (fun rf _ A => EddBe32EqSAsm.eddStatic ptr bsC K rf
          ∧ A = empAssertion) h := by
  intro h hp
  show (asrtOf RwRegion.empty _ ** bytesRegion ptr bsC) h
  refine sepConj_mono_left (fun h' hp' => ?_) h hp
  refine ⟨be32Rf ptr K vf, [], empAssertion, rfl, pcFree_emp,
    ⟨⟨?_, ?_, hlen⟩, rfl⟩, ?_⟩
  · show RegFile.get _ .x10 = ptr
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  · show RegFile.get _ .x11 = K
    rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
    rw [be32Rf, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
    exact if_pos rfl
  · rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
      regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
      edd_split_pre2,
      show be32Rf ptr K vf .x10 = ptr from if_pos rfl,
      show be32Rf ptr K vf .x11 = K from by
        rw [be32Rf, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl,
      regAtomsOf_congr (fun r => be32Rf ptr K vf r) vf eddScr13
        (fun r hr => by
          show (if r = .x10 then ptr else if r = .x11 then K else vf r)
            = vf r
          rw [if_neg (fun hc => (by decide : (Reg.x10 : Reg) ∉ eddScr13)
                (by rw [← hc]; exact hr)),
            if_neg (fun hc => (by decide : (Reg.x11 : Reg) ∉ eddScr13)
                (by rw [← hc]; exact hr))])]
    exact hp'

/-- Unpack: `edd_be32_eq`'s postcondition (with the check accepted)
    yields the `a0 = 1` atom, ownership of the rest, and the field bytes
    back. -/
private theorem edd_unpack_be32 (ptr K : Word) (bsC : List (BitVec 8))
    (hok : EddBe32EqSAsm.eddOk ptr bsC K) :
    ∀ h, asrtM ⟨ptr, bsC⟩ RwRegion.empty
        (fun rf _ A => rf.get .x10 = EddBe32EqSAsm.eddOut ptr bsC K
          ∧ A = empAssertion) h →
      ((((.x10 : Reg) ↦ᵣ (1 : Word)) ** regOwns eddScr14) **
        bytesRegion ptr bsC) h := by
  intro h hp
  have hp' : (asrtOf RwRegion.empty _ ** bytesRegion ptr bsC) h := hp
  refine sepConj_mono_left (fun h' hq => ?_) h hp'
  obtain ⟨rf, ws, A, hws, -, ⟨h10, rfl⟩, hh⟩ := hq
  obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
  rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
    regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    edd_split_post,
    show rf .x10 = (1 : Word) from by
      rw [show rf .x10 = rf.get .x10 from by
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
      rw [h10, EddBe32EqSAsm.eddOut, if_pos hok]] at hh
  exact sepConj_mono_right (regAtomsOf_to_regOwns _ _) h' hh

/-- The explicit callee-entry register file for a copy call. -/
private def mcRf (src dst nW : Word) (vf : Reg → Word) : RegFile :=
  fun r => if r = .x10 then src else if r = .x11 then dst
    else if r = .x12 then nW else vf r

/-- Pack: the caller's fifteen exposed atoms (with `a0 = src`,
    `a1 = dst`, `a2 = n`), the destination window, and the source bytes
    satisfy `edd_memcpy`'s call-site precondition. -/
private theorem edd_pack_mc (src dst : Word) (n : Nat)
    (bsS ws0 : List (BitVec 8)) (vf : Reg → Word) (hw : ws0.length = n) :
    ∀ h, (((((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** regAtomsOf vf eddScr12) **
        bytesRegion dst ws0) ** bytesRegion src bsS) h →
      asrtM ⟨src, bsS⟩ ⟨dst, n⟩
        (fun rf ws A => rf.get .x10 = src ∧ rf.get .x11 = dst ∧
          rf.get .x12 = BitVec.ofNat 64 n ∧ ws = ws0
          ∧ A = empAssertion) h := by
  intro h hp
  show (asrtOf ⟨dst, n⟩ _ ** bytesRegion src bsS) h
  refine sepConj_mono_left (fun h' hp' => ?_) h hp
  refine ⟨mcRf src dst (BitVec.ofNat 64 n) vf, ws0, empAssertion, hw,
    pcFree_emp, ⟨?_, ?_, ?_, rfl, rfl⟩, ?_⟩
  · show RegFile.get _ .x10 = src
    rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
    exact if_pos rfl
  · show RegFile.get _ .x11 = dst
    rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
    rw [mcRf, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
    exact if_pos rfl
  · show RegFile.get _ .x12 = BitVec.ofNat 64 n
    rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
    rw [mcRf, if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
      if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
    exact if_pos rfl
  · rw [sepConj_emp_right',
      regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
      edd_split_pre3,
      show mcRf src dst (BitVec.ofNat 64 n) vf .x10 = src from if_pos rfl,
      show mcRf src dst (BitVec.ofNat 64 n) vf .x11 = dst from by
        rw [mcRf, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
        exact if_pos rfl,
      show mcRf src dst (BitVec.ofNat 64 n) vf .x12 = BitVec.ofNat 64 n
        from by
        rw [mcRf, if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
          if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
        exact if_pos rfl,
      regAtomsOf_congr (fun r => mcRf src dst (BitVec.ofNat 64 n) vf r)
        vf eddScr12
        (fun r hr => by
          show (if r = .x10 then src else if r = .x11 then dst
            else if r = .x12 then BitVec.ofNat 64 n else vf r) = vf r
          rw [if_neg (fun hc => (by decide : (Reg.x10 : Reg) ∉ eddScr12)
                (by rw [← hc]; exact hr)),
            if_neg (fun hc => (by decide : (Reg.x11 : Reg) ∉ eddScr12)
                (by rw [← hc]; exact hr)),
            if_neg (fun hc => (by decide : (Reg.x12 : Reg) ∉ eddScr12)
                (by rw [← hc]; exact hr))])]
    exact hp'

/-- Unpack: `edd_memcpy`'s call-site postcondition yields the copied
    window, the source bytes back, and ownership of all fifteen exposed
    registers. -/
private theorem edd_unpack_mc (src dst : Word) (n : Nat)
    (bsS : List (BitVec 8)) (hlen : bsS.length = n) :
    ∀ h, asrtM ⟨src, bsS⟩ ⟨dst, n⟩
        (fun _ ws A => ws = bsS.take n ∧ A = empAssertion) h →
      ((regOwns exposedRegs ** bytesRegion dst bsS) **
        bytesRegion src bsS) h := by
  intro h hp
  have hp' : (asrtOf ⟨dst, n⟩ _ ** bytesRegion src bsS) h := hp
  refine sepConj_mono_left (fun h' hq => ?_) h hp'
  obtain ⟨rf, ws, A, -, -, ⟨rfl, rfl⟩, hh⟩ := hq
  rw [sepConj_emp_right',
    show bsS.take n = bsS from by rw [← hlen]; exact List.take_length,
    regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
  exact sepConj_mono_left (regAtomsOf_to_regOwns _ _) h' hh

/-! ## One `edd_be32_eq` call group -/

/-- Fuel monotonicity (the bound is an upper bound). -/
private theorem cps_fuel_mono {n m : Nat} {entry exit_ : Word}
    {cr : CodeReq} {P Q : Assertion} (hnm : n ≤ m)
    (h : cpsTripleWithin n entry exit_ cr P Q) :
    cpsTripleWithin m entry exit_ cr P Q := by
  intro R hR s hcr hp hpc
  obtain ⟨k, hk, rest⟩ := h R hR s hcr hp hpc
  exact ⟨k, Nat.le_trans hk hnm, rest⟩

set_option maxRecDepth 8000 in
/-- **One four-instruction check group**: the argument step into `a0`
    (hypothesis-supplied: `mv a0, s0` or `addi a0, s0, ofs`),
    `li a1, K`, `jal ra, edd_be32_eq`, and the not-taken `beq a0, x0`
    (the check accepted under `hok`, so the callee returned `a0 = 1`). -/
private theorem edd_check_group (G ptr K : Word) (joff : BitVec 21)
    (bofs : BitVec 13) (bsC : List (BitVec 8))
    (harg : ∀ v10 : Word, cpsTripleWithin 1 G (G + 4) eddbCode
        (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
        (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ eddDataPtr)))
    (hli : ∀ v11 : Word, cpsTripleWithin 1 (G + 4) (G + 8) eddbCode
        ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ K))
    (hjmem : ∀ a i, CodeReq.singleton (G + 8) (.JAL .x1 joff) a = some i →
      eddbCode a = some i)
    (hbmem : ∀ a i,
      CodeReq.singleton (G + 12) (.BEQ .x10 .x0 bofs) a = some i →
      eddbCode a = some i)
    (htarget : (G + 8) + signExtend21 joff = EddB + 304)
    (halign : ((G + 12) &&& ~~~(1 : Word)) = G + 12)
    (hwf : Region.wf ⟨ptr, bsC⟩)
    (hlen : 32 ≤ bsC.length)
    (hok : EddBe32EqSAsm.eddOk ptr bsC K) :
    cpsTripleWithin 636 G (G + 16) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion ptr bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion ptr bsC) := by
  -- Peel `ra` and the fifteen exposed registers to concrete valuations.
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns exposedRegs ** bytesRegion ptr bsC)
      (fun v1 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns exposedRegs (by decide)
      (P := ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion ptr bsC ** ((.x1 : Reg) ↦ᵣ v1))
      (fun vf => ?_))
  -- The callee triple over the bundle image, at return address `G + 12`.
  have hret := EddBe32EqSAsm.eddBe32Eq_retSpec ptr bsC K (EddB + 304)
    (G + 12) hwf halign
  rw [be32_flatten, be32_steps] at hret
  have hretB := cpsTripleWithin_extend_code be32_sub hret
  rw [show (G + 12 : Word) = (G + 8) + 4 from by
    rw [BitVec.add_assoc]; rfl] at hretB
  -- The linked call: `jal ra` composed with the callee's contract.
  have hcall := callWithin_spec (cr := eddbCode) (G + 8) (EddB + 304) v1
    joff 632 htarget hjmem (pcFree_asrtM _ _ _) hretB
  rw [show ((G + 8) + 4 : Word) = G + 12 from by
    rw [BitVec.add_assoc]; rfl] at hcall
  -- The four framed pieces.
  have hargF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ vf .x11) ** regAtomsOf vf eddScr13 **
      ((.x1 : Reg) ↦ᵣ v1) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion ptr bsC)
    (by edd_pcfree) (harg (vf .x10))
  have hliF := cpsTripleWithin_frameR
    ((((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ eddDataPtr)) **
      regAtomsOf vf eddScr13 ** ((.x1 : Reg) ↦ᵣ v1) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bsC)
    (by edd_pcfree) (hli (vf .x11))
  have hcallF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by edd_pcfree) hcall
  have hbeq := beq_spec_gen_within .x10 .x0 bofs (1 : Word) (0 : Word)
    (G + 12)
  have hBeq := cpsTripleWithin_extend_code hbmem
    (cpsBranchWithin_ntakenPath hbeq
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd (((sepConj_pure_right _).1 h_pure).2)
          (by decide : ¬((1 : Word) = 0))))
  rw [show (G + 12 : Word) + 4 = G + 16 from by
    rw [BitVec.add_assoc]; rfl] at hBeq
  have hBeqF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (G + 12)) ** regOwns eddScr14 **
      ((.x8 : Reg) ↦ᵣ eddDataPtr) ** bytesRegion ptr bsC)
    (by edd_pcfree) hBeq
  -- Compose.
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hargF hliF
    intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hcallF
    intro h hp
    have hp1 : (((((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ K) **
        regAtomsOf vf eddScr13) ** bytesRegion ptr bsC) **
        (((.x1 : Reg) ↦ᵣ v1) ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)))) h := by xperm_hyp hp
    have hp2 := sepConj_mono_left
      (edd_pack_be32 ptr K bsC vf hlen) h hp1
    xperm_hyp hp2
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hBeqF
    intro h hp
    have hp1 := sepConj_mono_left (sepConj_mono_right
      (edd_unpack_be32 ptr K bsC hok)) h hp
    xperm_hyp hp1
  refine cps_fuel_mono (by norm_num)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) s3)
  · rw [edd_split_pre2 vf] at hp
    xperm_hyp hp
  · have hq1 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    have hq2 : ((regOwn .x10 ** regOwns eddScr14) **
        (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion ptr bsC)) h := by
      have hq1a := sepConj_mono_left (sepConj_mono_left
        (regIs_to_regOwn .x10 (1 : Word))) h hq1
      have hq1b := sepConj_mono_right (sepConj_mono_left
        (regIs_to_regOwn .x1 (G + 12))) h hq1a
      xperm_hyp hq1b
    have hq3 := sepConj_mono_left edd_owns_recombine h hq2
    xperm_hyp hq3

/-! ## One `edd_memcpy` call group -/

/-- **One four-instruction copy group**: the three argument steps
    (`addi a0, s0, offS`, `mv/addi a1, s1(, offD)`, `li a2, n`) and
    `jal ra, edd_memcpy` composed with the #12805 call-site triple
    (hypothesis-supplied over the bundle image, `mcStatic` already
    discharged).  The destination window's `ws0` becomes the source
    bytes. -/
private theorem edd_copy_group (G src dst : Word) (joff : BitVec 21)
    (n ns : Nat) (bsS ws0 : List (BitVec 8))
    (harg10 : ∀ v : Word, cpsTripleWithin 1 G (G + 4) eddbCode
        (((.x10 : Reg) ↦ᵣ v) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
        (((.x10 : Reg) ↦ᵣ src) ** ((.x8 : Reg) ↦ᵣ eddDataPtr)))
    (harg11 : ∀ v : Word, cpsTripleWithin 1 (G + 4) (G + 8) eddbCode
        (((.x11 : Reg) ↦ᵣ v) ** ((.x9 : Reg) ↦ᵣ eddOutPtr))
        (((.x11 : Reg) ↦ᵣ dst) ** ((.x9 : Reg) ↦ᵣ eddOutPtr)))
    (harg12 : ∀ v : Word, cpsTripleWithin 1 (G + 8) (G + 12) eddbCode
        ((.x12 : Reg) ↦ᵣ v) ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n))
    (hjmem : ∀ a i,
      CodeReq.singleton (G + 12) (.JAL .x1 joff) a = some i →
      eddbCode a = some i)
    (htarget : (G + 12) + signExtend21 joff = EddB + 396)
    (hcallee : cpsTripleWithin ns (EddB + 396) (G + 16) eddbCode
        (((.x1 : Reg) ↦ᵣ (G + 16))
          ** asrtM ⟨src, bsS⟩ ⟨dst, n⟩
            (fun rf ws A => rf.get .x10 = src ∧ rf.get .x11 = dst ∧
              rf.get .x12 = BitVec.ofNat 64 n ∧ ws = ws0
              ∧ A = empAssertion))
        (((.x1 : Reg) ↦ᵣ (G + 16))
          ** asrtM ⟨src, bsS⟩ ⟨dst, n⟩
            (fun _ ws A => ws = bsS.take n ∧ A = empAssertion)))
    (hw : ws0.length = n) (hlenS : bsS.length = n) :
    cpsTripleWithin (4 + ns) G (G + 16) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion src bsS ** bytesRegion dst ws0)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion src bsS ** bytesRegion dst bsS) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn
      (P := ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr) **
        regOwns exposedRegs ** bytesRegion src bsS ** bytesRegion dst ws0)
      (fun v1 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns exposedRegs (by decide)
      (P := ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr) **
        bytesRegion src bsS ** bytesRegion dst ws0 **
        ((.x1 : Reg) ↦ᵣ v1))
      (fun vf => ?_))
  -- The linked call: `jal ra` composed with the call-site contract.
  rw [show (G + 16 : Word) = (G + 12) + 4 from by
    rw [BitVec.add_assoc]; rfl] at hcallee
  have hcall := callWithin_spec (cr := eddbCode) (G + 12) (EddB + 396) v1
    joff ns htarget hjmem (pcFree_asrtM _ _ _) hcallee
  rw [show ((G + 12) + 4 : Word) = G + 16 from by
    rw [BitVec.add_assoc]; rfl] at hcall
  -- The four framed pieces.
  have harg10F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ vf .x11) ** ((.x12 : Reg) ↦ᵣ vf .x12) **
      regAtomsOf vf eddScr12 ** ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      ((.x1 : Reg) ↦ᵣ v1) ** bytesRegion src bsS ** bytesRegion dst ws0)
    (by edd_pcfree) (harg10 (vf .x10))
  have harg11F := cpsTripleWithin_frameR
    ((((.x10 : Reg) ↦ᵣ src) ** ((.x8 : Reg) ↦ᵣ eddDataPtr)) **
      ((.x12 : Reg) ↦ᵣ vf .x12) ** regAtomsOf vf eddScr12 **
      ((.x1 : Reg) ↦ᵣ v1) ** bytesRegion src bsS ** bytesRegion dst ws0)
    (by edd_pcfree) (harg11 (vf .x11))
  have harg12F := cpsTripleWithin_frameR
    ((((.x10 : Reg) ↦ᵣ src) ** ((.x8 : Reg) ↦ᵣ eddDataPtr)) **
      (((.x11 : Reg) ↦ᵣ dst) ** ((.x9 : Reg) ↦ᵣ eddOutPtr)) **
      regAtomsOf vf eddScr12 ** ((.x1 : Reg) ↦ᵣ v1) **
      bytesRegion src bsS ** bytesRegion dst ws0)
    (by edd_pcfree) (harg12 (vf .x12))
  have hcallF := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr))
    (by edd_pcfree) hcall
  -- Compose.
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ harg10F harg11F
    intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 harg12F
    intro h hp; xperm_hyp hp
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hcallF
    intro h hp
    have hp1 : ((((((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** regAtomsOf vf eddScr12) **
        bytesRegion dst ws0) ** bytesRegion src bsS) **
        (((.x1 : Reg) ↦ᵣ v1) ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
          ((.x9 : Reg) ↦ᵣ eddOutPtr))) h := by xperm_hyp hp
    have hp2 := sepConj_mono_left
      (edd_pack_mc src dst n bsS ws0 vf hw) h hp1
    xperm_hyp hp2
  refine cps_fuel_mono (by omega)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) s3)
  · rw [edd_split_pre3 vf] at hp
    xperm_hyp hp
  · have hq1 := sepConj_mono_left (sepConj_mono_right
      (edd_unpack_mc src dst n bsS hlenS)) h hq
    have hq2 := sepConj_mono_left (sepConj_mono_left
      (regIs_to_regOwn .x1 (G + 16))) h hq1
    xperm_hyp hq2

/-! ## Ownership assembly helpers for the whole-path composition -/

/-- The exposed registers the routine's contract does not pin on entry
    (`t0`/`a0`/`a1`/`a2` are pinned; these eleven are merely owned). -/
def eddScrPre : List Reg :=
  [.x6, .x7, .x28, .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17]

private theorem edd_owns_assemble :
    ∀ h, ((regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12) **
        regOwns eddScrPre) h →
      regOwns exposedRegs h := by
  intro h hp
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] h
  simp only [regOwns_cons, regOwns_nil]
  simp only [eddScrPre, regOwns_cons, regOwns_nil] at hp
  xperm_hyp hp

private theorem edd_owns_split :
    ∀ h, regOwns exposedRegs h → (regOwn .x10 ** regOwns eddScr14) h := by
  intro h hp
  have hp' : regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] h := hp
  simp only [regOwns_cons, regOwns_nil] at hp'
  simp only [eddScr14, regOwns_cons, regOwns_nil]
  xperm_hyp hp'

/-! ## The fifteen call groups at their bundle addresses -/
set_option maxRecDepth 100000 in
/-- Check group 1: `edd_be32_eq(data+0, 160)` at `EddB + 32`. -/
private theorem edd_check_g1 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨eddDataPtr, bsC⟩)
    (hok : EddBe32EqSAsm.eddOk eddDataPtr bsC (160 : Word)) :
    cpsTripleWithin 636 (EddB + 32) (EddB + 48) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion eddDataPtr bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion eddDataPtr bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 32)
      ((EddB + 32) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ eddDataPtr) ** ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := mv_spec_gen_within .x10 .x8 eddDataPtr v10 (EddB + 32)
      (by decide)
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 8 _ (EddB + 32)
        (by rw [show (4 * 8 : Nat) = 32 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 32) + 4)
      ((EddB + 32) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (160 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (160 : Word)
      ((EddB + 32) + 4) (by decide)
    rw [show ((EddB + 32) + 4) + 4 = (EddB + 32) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 9 _ ((EddB + 32) + 4)
      (by rw [show (4 * 9 : Nat) = 36 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 32) eddDataPtr (160 : Word)
    (264 : BitVec 21) (236 : BitVec 13) bsC harg hli
    (eddb_mem 10 (.JAL .x1 (264 : BitVec 21)) ((EddB + 32) + 8)
      (by rw [show (4 * 10 : Nat) = 40 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 11 (.BEQ .x10 .x0 (236 : BitVec 13)) ((EddB + 32) + 12)
      (by rw [show (4 * 11 : Nat) = 44 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (264 : BitVec 21) = (264 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 32) + 16 = EddB + 48 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 2: `edd_be32_eq(data+32, 256)` at `EddB + 48`. -/
private theorem edd_check_g2 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 32), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 32) bsC (256 : Word)) :
    cpsTripleWithin 636 (EddB + 48) (EddB + 64) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 32) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 32) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 48)
      ((EddB + 48) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 32)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (32 : BitVec 12) (EddB + 48) (by decide)
    rw [show signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 32
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 12 _ (EddB + 48)
        (by rw [show (4 * 12 : Nat) = 48 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 48) + 4)
      ((EddB + 48) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (256 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (256 : Word)
      ((EddB + 48) + 4) (by decide)
    rw [show ((EddB + 48) + 4) + 4 = (EddB + 48) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 13 _ ((EddB + 48) + 4)
      (by rw [show (4 * 13 : Nat) = 52 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 48) (eddDataPtr + BitVec.ofNat 64 32) (256 : Word)
    (248 : BitVec 21) (220 : BitVec 13) bsC harg hli
    (eddb_mem 14 (.JAL .x1 (248 : BitVec 21)) ((EddB + 48) + 8)
      (by rw [show (4 * 14 : Nat) = 56 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 15 (.BEQ .x10 .x0 (220 : BitVec 13)) ((EddB + 48) + 12)
      (by rw [show (4 * 15 : Nat) = 60 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (248 : BitVec 21) = (248 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 48) + 16 = EddB + 64 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 3: `edd_be32_eq(data+64, 320)` at `EddB + 64`. -/
private theorem edd_check_g3 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 64), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 64) bsC (320 : Word)) :
    cpsTripleWithin 636 (EddB + 64) (EddB + 80) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 64) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 64) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 64)
      ((EddB + 64) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 64)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (64 : BitVec 12) (EddB + 64) (by decide)
    rw [show signExtend12 (64 : BitVec 12) = BitVec.ofNat 64 64
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 16 _ (EddB + 64)
        (by rw [show (4 * 16 : Nat) = 64 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 64) + 4)
      ((EddB + 64) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (320 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (320 : Word)
      ((EddB + 64) + 4) (by decide)
    rw [show ((EddB + 64) + 4) + 4 = (EddB + 64) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 17 _ ((EddB + 64) + 4)
      (by rw [show (4 * 17 : Nat) = 68 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 64) (eddDataPtr + BitVec.ofNat 64 64) (320 : Word)
    (232 : BitVec 21) (204 : BitVec 13) bsC harg hli
    (eddb_mem 18 (.JAL .x1 (232 : BitVec 21)) ((EddB + 64) + 8)
      (by rw [show (4 * 18 : Nat) = 72 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 19 (.BEQ .x10 .x0 (204 : BitVec 13)) ((EddB + 64) + 12)
      (by rw [show (4 * 19 : Nat) = 76 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (232 : BitVec 21) = (232 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 64) + 16 = EddB + 80 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 4: `edd_be32_eq(data+96, 384)` at `EddB + 80`. -/
private theorem edd_check_g4 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 96), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 96) bsC (384 : Word)) :
    cpsTripleWithin 636 (EddB + 80) (EddB + 96) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 96) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 96) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 80)
      ((EddB + 80) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 96)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (96 : BitVec 12) (EddB + 80) (by decide)
    rw [show signExtend12 (96 : BitVec 12) = BitVec.ofNat 64 96
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 20 _ (EddB + 80)
        (by rw [show (4 * 20 : Nat) = 80 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 80) + 4)
      ((EddB + 80) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (384 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (384 : Word)
      ((EddB + 80) + 4) (by decide)
    rw [show ((EddB + 80) + 4) + 4 = (EddB + 80) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 21 _ ((EddB + 80) + 4)
      (by rw [show (4 * 21 : Nat) = 84 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 80) (eddDataPtr + BitVec.ofNat 64 96) (384 : Word)
    (216 : BitVec 21) (188 : BitVec 13) bsC harg hli
    (eddb_mem 22 (.JAL .x1 (216 : BitVec 21)) ((EddB + 80) + 8)
      (by rw [show (4 * 22 : Nat) = 88 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 23 (.BEQ .x10 .x0 (188 : BitVec 13)) ((EddB + 80) + 12)
      (by rw [show (4 * 23 : Nat) = 92 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (216 : BitVec 21) = (216 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 80) + 16 = EddB + 96 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 5: `edd_be32_eq(data+128, 512)` at `EddB + 96`. -/
private theorem edd_check_g5 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 128), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 128) bsC (512 : Word)) :
    cpsTripleWithin 636 (EddB + 96) (EddB + 112) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 128) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 128) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 96)
      ((EddB + 96) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 128)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (128 : BitVec 12) (EddB + 96) (by decide)
    rw [show signExtend12 (128 : BitVec 12) = BitVec.ofNat 64 128
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 24 _ (EddB + 96)
        (by rw [show (4 * 24 : Nat) = 96 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 96) + 4)
      ((EddB + 96) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (512 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (512 : Word)
      ((EddB + 96) + 4) (by decide)
    rw [show ((EddB + 96) + 4) + 4 = (EddB + 96) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 25 _ ((EddB + 96) + 4)
      (by rw [show (4 * 25 : Nat) = 100 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 96) (eddDataPtr + BitVec.ofNat 64 128) (512 : Word)
    (200 : BitVec 21) (172 : BitVec 13) bsC harg hli
    (eddb_mem 26 (.JAL .x1 (200 : BitVec 21)) ((EddB + 96) + 8)
      (by rw [show (4 * 26 : Nat) = 104 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 27 (.BEQ .x10 .x0 (172 : BitVec 13)) ((EddB + 96) + 12)
      (by rw [show (4 * 27 : Nat) = 108 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (200 : BitVec 21) = (200 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 96) + 16 = EddB + 112 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 6: `edd_be32_eq(data+160, 48)` at `EddB + 112`. -/
private theorem edd_check_g6 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 160), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 160) bsC (48 : Word)) :
    cpsTripleWithin 636 (EddB + 112) (EddB + 128) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 160) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 160) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 112)
      ((EddB + 112) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 160)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (160 : BitVec 12) (EddB + 112) (by decide)
    rw [show signExtend12 (160 : BitVec 12) = BitVec.ofNat 64 160
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 28 _ (EddB + 112)
        (by rw [show (4 * 28 : Nat) = 112 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 112) + 4)
      ((EddB + 112) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (48 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (48 : Word)
      ((EddB + 112) + 4) (by decide)
    rw [show ((EddB + 112) + 4) + 4 = (EddB + 112) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 29 _ ((EddB + 112) + 4)
      (by rw [show (4 * 29 : Nat) = 116 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 112) (eddDataPtr + BitVec.ofNat 64 160) (48 : Word)
    (184 : BitVec 21) (156 : BitVec 13) bsC harg hli
    (eddb_mem 30 (.JAL .x1 (184 : BitVec 21)) ((EddB + 112) + 8)
      (by rw [show (4 * 30 : Nat) = 120 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 31 (.BEQ .x10 .x0 (156 : BitVec 13)) ((EddB + 112) + 12)
      (by rw [show (4 * 31 : Nat) = 124 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (184 : BitVec 21) = (184 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 112) + 16 = EddB + 128 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 7: `edd_be32_eq(data+256, 32)` at `EddB + 128`. -/
private theorem edd_check_g7 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 256), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 256) bsC (32 : Word)) :
    cpsTripleWithin 636 (EddB + 128) (EddB + 144) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 256) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 256) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 128)
      ((EddB + 128) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 256)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (256 : BitVec 12) (EddB + 128) (by decide)
    rw [show signExtend12 (256 : BitVec 12) = BitVec.ofNat 64 256
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 32 _ (EddB + 128)
        (by rw [show (4 * 32 : Nat) = 128 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 128) + 4)
      ((EddB + 128) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (32 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (32 : Word)
      ((EddB + 128) + 4) (by decide)
    rw [show ((EddB + 128) + 4) + 4 = (EddB + 128) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 33 _ ((EddB + 128) + 4)
      (by rw [show (4 * 33 : Nat) = 132 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 128) (eddDataPtr + BitVec.ofNat 64 256) (32 : Word)
    (168 : BitVec 21) (140 : BitVec 13) bsC harg hli
    (eddb_mem 34 (.JAL .x1 (168 : BitVec 21)) ((EddB + 128) + 8)
      (by rw [show (4 * 34 : Nat) = 136 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 35 (.BEQ .x10 .x0 (140 : BitVec 13)) ((EddB + 128) + 12)
      (by rw [show (4 * 35 : Nat) = 140 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (168 : BitVec 21) = (168 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 128) + 16 = EddB + 144 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 8: `edd_be32_eq(data+320, 8)` at `EddB + 144`. -/
private theorem edd_check_g8 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 320), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 320) bsC (8 : Word)) :
    cpsTripleWithin 636 (EddB + 144) (EddB + 160) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 320) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 320) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 144)
      ((EddB + 144) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 320)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (320 : BitVec 12) (EddB + 144) (by decide)
    rw [show signExtend12 (320 : BitVec 12) = BitVec.ofNat 64 320
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 36 _ (EddB + 144)
        (by rw [show (4 * 36 : Nat) = 144 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 144) + 4)
      ((EddB + 144) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (8 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (8 : Word)
      ((EddB + 144) + 4) (by decide)
    rw [show ((EddB + 144) + 4) + 4 = (EddB + 144) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 37 _ ((EddB + 144) + 4)
      (by rw [show (4 * 37 : Nat) = 148 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 144) (eddDataPtr + BitVec.ofNat 64 320) (8 : Word)
    (152 : BitVec 21) (124 : BitVec 13) bsC harg hli
    (eddb_mem 38 (.JAL .x1 (152 : BitVec 21)) ((EddB + 144) + 8)
      (by rw [show (4 * 38 : Nat) = 152 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 39 (.BEQ .x10 .x0 (124 : BitVec 13)) ((EddB + 144) + 12)
      (by rw [show (4 * 39 : Nat) = 156 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (152 : BitVec 21) = (152 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 144) + 16 = EddB + 160 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 9: `edd_be32_eq(data+384, 96)` at `EddB + 160`. -/
private theorem edd_check_g9 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 384), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 384) bsC (96 : Word)) :
    cpsTripleWithin 636 (EddB + 160) (EddB + 176) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 384) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 384) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 160)
      ((EddB + 160) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 384)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (384 : BitVec 12) (EddB + 160) (by decide)
    rw [show signExtend12 (384 : BitVec 12) = BitVec.ofNat 64 384
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 40 _ (EddB + 160)
        (by rw [show (4 * 40 : Nat) = 160 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 160) + 4)
      ((EddB + 160) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (96 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (96 : Word)
      ((EddB + 160) + 4) (by decide)
    rw [show ((EddB + 160) + 4) + 4 = (EddB + 160) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 41 _ ((EddB + 160) + 4)
      (by rw [show (4 * 41 : Nat) = 164 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 160) (eddDataPtr + BitVec.ofNat 64 384) (96 : Word)
    (136 : BitVec 21) (108 : BitVec 13) bsC harg hli
    (eddb_mem 42 (.JAL .x1 (136 : BitVec 21)) ((EddB + 160) + 8)
      (by rw [show (4 * 42 : Nat) = 168 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 43 (.BEQ .x10 .x0 (108 : BitVec 13)) ((EddB + 160) + 12)
      (by rw [show (4 * 43 : Nat) = 172 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (136 : BitVec 21) = (136 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 160) + 16 = EddB + 176 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Check group 10: `edd_be32_eq(data+512, 8)` at `EddB + 176`. -/
private theorem edd_check_g10 (bsC : List (BitVec 8))
    (hlen : 32 ≤ bsC.length)
    (hwf : Region.wf ⟨(eddDataPtr + BitVec.ofNat 64 512), bsC⟩)
    (hok : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 512) bsC (8 : Word)) :
    cpsTripleWithin 636 (EddB + 176) (EddB + 192) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 512) bsC)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 512) bsC) := by
  have harg : ∀ v10 : Word, cpsTripleWithin 1 (EddB + 176)
      ((EddB + 176) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 512)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v10
    have h := addi_spec_gen_within .x10 .x8 v10 eddDataPtr
      (512 : BitVec 12) (EddB + 176) (by decide)
    rw [show signExtend12 (512 : BitVec 12) = BitVec.ofNat 64 512
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 44 _ (EddB + 176)
        (by rw [show (4 * 44 : Nat) = 176 from rfl]; rfl)
        (by omega) rfl) h)
  have hli : ∀ v11 : Word, cpsTripleWithin 1 ((EddB + 176) + 4)
      ((EddB + 176) + 8) eddbCode
      ((.x11 : Reg) ↦ᵣ v11) ((.x11 : Reg) ↦ᵣ (8 : Word)) := by
    intro v11
    have h := li_spec_gen_within .x11 v11 (8 : Word)
      ((EddB + 176) + 4) (by decide)
    rw [show ((EddB + 176) + 4) + 4 = (EddB + 176) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 45 _ ((EddB + 176) + 4)
      (by rw [show (4 * 45 : Nat) = 180 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_check_group (EddB + 176) (eddDataPtr + BitVec.ofNat 64 512) (8 : Word)
    (120 : BitVec 21) (92 : BitVec 13) bsC harg hli
    (eddb_mem 46 (.JAL .x1 (120 : BitVec 21)) ((EddB + 176) + 8)
      (by rw [show (4 * 46 : Nat) = 184 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (eddb_mem 47 (.BEQ .x10 .x0 (92 : BitVec 13)) ((EddB + 176) + 12)
      (by rw [show (4 * 47 : Nat) = 188 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (120 : BitVec 21) = (120 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    (by decide) hwf hlen hok
  rwa [show (EddB + 176) + 16 = EddB + 192 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Copy group 1: `edd_memcpy(data+192 → out+0, 48)` at
    `EddB + 192` (the #12805 `pubkey` call site). -/
private theorem edd_copy_c1 (bsS ws0 : List (BitVec 8))
    (hlenS : bsS.length = 48) (hw : ws0.length = 48) :
    cpsTripleWithin 342 (EddB + 192) (EddB + 208) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 192) bsS ** bytesRegion eddOutPtr ws0)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 192) bsS ** bytesRegion eddOutPtr bsS) := by
  have hcs := EvmAsm.Codegen.eddMemcpy_pubkey_callsite bsS ws0 (EddB + 396)
    ((EddB + 192) + 16) hlenS hw (by decide)
  rw [EddMemcpySAsm.mcDeriv_flatten_ghost_free, mc_flatten_at,
    mc_steps_ghost_free, mc_steps_48] at hcs
  rw [show eddOutPtr + BitVec.ofNat 64 0 = eddOutPtr from by decide] at hcs
  have hcsB := cpsTripleWithin_extend_code mc_sub hcs
  have harg10 : ∀ v : Word, cpsTripleWithin 1 (EddB + 192)
      ((EddB + 192) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 192)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v
    have h := addi_spec_gen_within .x10 .x8 v eddDataPtr
      (192 : BitVec 12) (EddB + 192) (by decide)
    rw [show signExtend12 (192 : BitVec 12) = BitVec.ofNat 64 192
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 48 _ (EddB + 192)
        (by rw [show (4 * 48 : Nat) = 192 from rfl]; rfl)
        (by omega) rfl) h)
  have harg11 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 192) + 4)
      ((EddB + 192) + 8) eddbCode
      (((.x11 : Reg) ↦ᵣ v) ** ((.x9 : Reg) ↦ᵣ eddOutPtr))
      (((.x11 : Reg) ↦ᵣ eddOutPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr)) := by
    intro v
    have h := mv_spec_gen_within .x11 .x9 eddOutPtr v ((EddB + 192) + 4)
      (by decide)
    rw [show ((EddB + 192) + 4) + 4 = (EddB + 192) + 8 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 49 _ ((EddB + 192) + 4)
        (by rw [show (4 * 49 : Nat) = 196 from rfl, BitVec.add_assoc]
            rfl)
        (by omega) rfl) h)
  have harg12 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 192) + 8)
      ((EddB + 192) + 12) eddbCode
      ((.x12 : Reg) ↦ᵣ v) ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 48) := by
    intro v
    have h := li_spec_gen_within .x12 v (BitVec.ofNat 64 48)
      ((EddB + 192) + 8) (by decide)
    rw [show ((EddB + 192) + 8) + 4 = (EddB + 192) + 12 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 50 _ ((EddB + 192) + 8)
      (by rw [show (4 * 50 : Nat) = 200 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_copy_group (EddB + 192) (eddDataPtr + BitVec.ofNat 64 192) eddOutPtr
    (192 : BitVec 21) 48 338 bsS ws0 harg10 harg11 harg12
    (eddb_mem 51 (.JAL .x1 (192 : BitVec 21)) ((EddB + 192) + 12)
      (by rw [show (4 * 51 : Nat) = 204 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (192 : BitVec 21) = (192 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    hcsB hw hlenS
  rwa [show (EddB + 192) + 16 = EddB + 208 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Copy group 2: `edd_memcpy(data+288 → out+48, 32)` at
    `EddB + 208` (the #12805 `wc` call site). -/
private theorem edd_copy_c2 (bsS ws0 : List (BitVec 8))
    (hlenS : bsS.length = 32) (hw : ws0.length = 32) :
    cpsTripleWithin 230 (EddB + 208) (EddB + 224) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 288) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 48) ws0)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 288) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 48) bsS) := by
  have hcs := EvmAsm.Codegen.eddMemcpy_wc_callsite bsS ws0 (EddB + 396)
    ((EddB + 208) + 16) hlenS hw (by decide)
  rw [EddMemcpySAsm.mcDeriv_flatten_ghost_free, mc_flatten_at,
    mc_steps_ghost_free, mc_steps_32] at hcs

  have hcsB := cpsTripleWithin_extend_code mc_sub hcs
  have harg10 : ∀ v : Word, cpsTripleWithin 1 (EddB + 208)
      ((EddB + 208) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 288)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v
    have h := addi_spec_gen_within .x10 .x8 v eddDataPtr
      (288 : BitVec 12) (EddB + 208) (by decide)
    rw [show signExtend12 (288 : BitVec 12) = BitVec.ofNat 64 288
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 52 _ (EddB + 208)
        (by rw [show (4 * 52 : Nat) = 208 from rfl]; rfl)
        (by omega) rfl) h)
  have harg11 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 208) + 4)
      ((EddB + 208) + 8) eddbCode
      (((.x11 : Reg) ↦ᵣ v) ** ((.x9 : Reg) ↦ᵣ eddOutPtr))
      (((.x11 : Reg) ↦ᵣ (eddOutPtr + BitVec.ofNat 64 48)) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr)) := by
    intro v
    have h := addi_spec_gen_within .x11 .x9 v eddOutPtr
      (48 : BitVec 12) ((EddB + 208) + 4) (by decide)
    rw [show signExtend12 (48 : BitVec 12) = BitVec.ofNat 64 48
        from by decide,
      show ((EddB + 208) + 4) + 4 = (EddB + 208) + 8 from by
        rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 53 _ ((EddB + 208) + 4)
        (by rw [show (4 * 53 : Nat) = 212 from rfl, BitVec.add_assoc]
            rfl)
        (by omega) rfl) h)
  have harg12 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 208) + 8)
      ((EddB + 208) + 12) eddbCode
      ((.x12 : Reg) ↦ᵣ v) ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 32) := by
    intro v
    have h := li_spec_gen_within .x12 v (BitVec.ofNat 64 32)
      ((EddB + 208) + 8) (by decide)
    rw [show ((EddB + 208) + 8) + 4 = (EddB + 208) + 12 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 54 _ ((EddB + 208) + 8)
      (by rw [show (4 * 54 : Nat) = 216 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_copy_group (EddB + 208) (eddDataPtr + BitVec.ofNat 64 288) (eddOutPtr + BitVec.ofNat 64 48)
    (176 : BitVec 21) 32 226 bsS ws0 harg10 harg11 harg12
    (eddb_mem 55 (.JAL .x1 (176 : BitVec 21)) ((EddB + 208) + 12)
      (by rw [show (4 * 55 : Nat) = 220 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (176 : BitVec 21) = (176 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    hcsB hw hlenS
  rwa [show (EddB + 208) + 16 = EddB + 224 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Copy group 3: `edd_memcpy(data+352 → out+80, 8)` at
    `EddB + 224` (the #12805 `amount` call site). -/
private theorem edd_copy_c3 (bsS ws0 : List (BitVec 8))
    (hlenS : bsS.length = 8) (hw : ws0.length = 8) :
    cpsTripleWithin 62 (EddB + 224) (EddB + 240) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 352) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 80) ws0)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 352) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 80) bsS) := by
  have hcs := EvmAsm.Codegen.eddMemcpy_amount_callsite bsS ws0 (EddB + 396)
    ((EddB + 224) + 16) hlenS hw (by decide)
  rw [EddMemcpySAsm.mcDeriv_flatten_ghost_free, mc_flatten_at,
    mc_steps_ghost_free, mc_steps_8] at hcs

  have hcsB := cpsTripleWithin_extend_code mc_sub hcs
  have harg10 : ∀ v : Word, cpsTripleWithin 1 (EddB + 224)
      ((EddB + 224) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 352)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v
    have h := addi_spec_gen_within .x10 .x8 v eddDataPtr
      (352 : BitVec 12) (EddB + 224) (by decide)
    rw [show signExtend12 (352 : BitVec 12) = BitVec.ofNat 64 352
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 56 _ (EddB + 224)
        (by rw [show (4 * 56 : Nat) = 224 from rfl]; rfl)
        (by omega) rfl) h)
  have harg11 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 224) + 4)
      ((EddB + 224) + 8) eddbCode
      (((.x11 : Reg) ↦ᵣ v) ** ((.x9 : Reg) ↦ᵣ eddOutPtr))
      (((.x11 : Reg) ↦ᵣ (eddOutPtr + BitVec.ofNat 64 80)) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr)) := by
    intro v
    have h := addi_spec_gen_within .x11 .x9 v eddOutPtr
      (80 : BitVec 12) ((EddB + 224) + 4) (by decide)
    rw [show signExtend12 (80 : BitVec 12) = BitVec.ofNat 64 80
        from by decide,
      show ((EddB + 224) + 4) + 4 = (EddB + 224) + 8 from by
        rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 57 _ ((EddB + 224) + 4)
        (by rw [show (4 * 57 : Nat) = 228 from rfl, BitVec.add_assoc]
            rfl)
        (by omega) rfl) h)
  have harg12 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 224) + 8)
      ((EddB + 224) + 12) eddbCode
      ((.x12 : Reg) ↦ᵣ v) ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 8) := by
    intro v
    have h := li_spec_gen_within .x12 v (BitVec.ofNat 64 8)
      ((EddB + 224) + 8) (by decide)
    rw [show ((EddB + 224) + 8) + 4 = (EddB + 224) + 12 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 58 _ ((EddB + 224) + 8)
      (by rw [show (4 * 58 : Nat) = 232 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_copy_group (EddB + 224) (eddDataPtr + BitVec.ofNat 64 352) (eddOutPtr + BitVec.ofNat 64 80)
    (160 : BitVec 21) 8 58 bsS ws0 harg10 harg11 harg12
    (eddb_mem 59 (.JAL .x1 (160 : BitVec 21)) ((EddB + 224) + 12)
      (by rw [show (4 * 59 : Nat) = 236 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (160 : BitVec 21) = (160 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    hcsB hw hlenS
  rwa [show (EddB + 224) + 16 = EddB + 240 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Copy group 4: `edd_memcpy(data+416 → out+88, 96)` at
    `EddB + 240` (the #12805 `sig` call site). -/
private theorem edd_copy_c4 (bsS ws0 : List (BitVec 8))
    (hlenS : bsS.length = 96) (hw : ws0.length = 96) :
    cpsTripleWithin 678 (EddB + 240) (EddB + 256) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 416) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 88) ws0)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 416) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 88) bsS) := by
  have hcs := EvmAsm.Codegen.eddMemcpy_sig_callsite bsS ws0 (EddB + 396)
    ((EddB + 240) + 16) hlenS hw (by decide)
  rw [EddMemcpySAsm.mcDeriv_flatten_ghost_free, mc_flatten_at,
    mc_steps_ghost_free, mc_steps_96] at hcs

  have hcsB := cpsTripleWithin_extend_code mc_sub hcs
  have harg10 : ∀ v : Word, cpsTripleWithin 1 (EddB + 240)
      ((EddB + 240) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 416)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v
    have h := addi_spec_gen_within .x10 .x8 v eddDataPtr
      (416 : BitVec 12) (EddB + 240) (by decide)
    rw [show signExtend12 (416 : BitVec 12) = BitVec.ofNat 64 416
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 60 _ (EddB + 240)
        (by rw [show (4 * 60 : Nat) = 240 from rfl]; rfl)
        (by omega) rfl) h)
  have harg11 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 240) + 4)
      ((EddB + 240) + 8) eddbCode
      (((.x11 : Reg) ↦ᵣ v) ** ((.x9 : Reg) ↦ᵣ eddOutPtr))
      (((.x11 : Reg) ↦ᵣ (eddOutPtr + BitVec.ofNat 64 88)) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr)) := by
    intro v
    have h := addi_spec_gen_within .x11 .x9 v eddOutPtr
      (88 : BitVec 12) ((EddB + 240) + 4) (by decide)
    rw [show signExtend12 (88 : BitVec 12) = BitVec.ofNat 64 88
        from by decide,
      show ((EddB + 240) + 4) + 4 = (EddB + 240) + 8 from by
        rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 61 _ ((EddB + 240) + 4)
        (by rw [show (4 * 61 : Nat) = 244 from rfl, BitVec.add_assoc]
            rfl)
        (by omega) rfl) h)
  have harg12 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 240) + 8)
      ((EddB + 240) + 12) eddbCode
      ((.x12 : Reg) ↦ᵣ v) ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 96) := by
    intro v
    have h := li_spec_gen_within .x12 v (BitVec.ofNat 64 96)
      ((EddB + 240) + 8) (by decide)
    rw [show ((EddB + 240) + 8) + 4 = (EddB + 240) + 12 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 62 _ ((EddB + 240) + 8)
      (by rw [show (4 * 62 : Nat) = 248 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_copy_group (EddB + 240) (eddDataPtr + BitVec.ofNat 64 416) (eddOutPtr + BitVec.ofNat 64 88)
    (144 : BitVec 21) 96 674 bsS ws0 harg10 harg11 harg12
    (eddb_mem 63 (.JAL .x1 (144 : BitVec 21)) ((EddB + 240) + 12)
      (by rw [show (4 * 63 : Nat) = 252 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (144 : BitVec 21) = (144 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    hcsB hw hlenS
  rwa [show (EddB + 240) + 16 = EddB + 256 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 100000 in
/-- Copy group 5: `edd_memcpy(data+544 → out+184, 8)` at
    `EddB + 256` (the #12805 `index` call site). -/
private theorem edd_copy_c5 (bsS ws0 : List (BitVec 8))
    (hlenS : bsS.length = 8) (hw : ws0.length = 8) :
    cpsTripleWithin 62 (EddB + 256) (EddB + 272) eddbCode
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 544) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 184) ws0)
      (regOwn .x1 ** ((.x8 : Reg) ↦ᵣ eddDataPtr) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr) ** regOwns exposedRegs **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 544) bsS ** bytesRegion (eddOutPtr + BitVec.ofNat 64 184) bsS) := by
  have hcs := EvmAsm.Codegen.eddMemcpy_index_callsite bsS ws0 (EddB + 396)
    ((EddB + 256) + 16) hlenS hw (by decide)
  rw [EddMemcpySAsm.mcDeriv_flatten_ghost_free, mc_flatten_at,
    mc_steps_ghost_free, mc_steps_8] at hcs

  have hcsB := cpsTripleWithin_extend_code mc_sub hcs
  have harg10 : ∀ v : Word, cpsTripleWithin 1 (EddB + 256)
      ((EddB + 256) + 4) eddbCode
      (((.x10 : Reg) ↦ᵣ v) ** ((.x8 : Reg) ↦ᵣ eddDataPtr))
      (((.x10 : Reg) ↦ᵣ (eddDataPtr + BitVec.ofNat 64 544)) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr)) := by
    intro v
    have h := addi_spec_gen_within .x10 .x8 v eddDataPtr
      (544 : BitVec 12) (EddB + 256) (by decide)
    rw [show signExtend12 (544 : BitVec 12) = BitVec.ofNat 64 544
      from by decide] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 64 _ (EddB + 256)
        (by rw [show (4 * 64 : Nat) = 256 from rfl]; rfl)
        (by omega) rfl) h)
  have harg11 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 256) + 4)
      ((EddB + 256) + 8) eddbCode
      (((.x11 : Reg) ↦ᵣ v) ** ((.x9 : Reg) ↦ᵣ eddOutPtr))
      (((.x11 : Reg) ↦ᵣ (eddOutPtr + BitVec.ofNat 64 184)) **
        ((.x9 : Reg) ↦ᵣ eddOutPtr)) := by
    intro v
    have h := addi_spec_gen_within .x11 .x9 v eddOutPtr
      (184 : BitVec 12) ((EddB + 256) + 4) (by decide)
    rw [show signExtend12 (184 : BitVec 12) = BitVec.ofNat 64 184
        from by decide,
      show ((EddB + 256) + 4) + 4 = (EddB + 256) + 8 from by
        rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_extend_code (eddb_mem 65 _ ((EddB + 256) + 4)
        (by rw [show (4 * 65 : Nat) = 260 from rfl, BitVec.add_assoc]
            rfl)
        (by omega) rfl) h)
  have harg12 : ∀ v : Word, cpsTripleWithin 1 ((EddB + 256) + 8)
      ((EddB + 256) + 12) eddbCode
      ((.x12 : Reg) ↦ᵣ v) ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 8) := by
    intro v
    have h := li_spec_gen_within .x12 v (BitVec.ofNat 64 8)
      ((EddB + 256) + 8) (by decide)
    rw [show ((EddB + 256) + 8) + 4 = (EddB + 256) + 12 from by
      rw [BitVec.add_assoc]; rfl] at h
    exact cpsTripleWithin_extend_code (eddb_mem 66 _ ((EddB + 256) + 8)
      (by rw [show (4 * 66 : Nat) = 264 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl) h
  have hg := edd_copy_group (EddB + 256) (eddDataPtr + BitVec.ofNat 64 544) (eddOutPtr + BitVec.ofNat 64 184)
    (128 : BitVec 21) 8 58 bsS ws0 harg10 harg11 harg12
    (eddb_mem 67 (.JAL .x1 (128 : BitVec 21)) ((EddB + 256) + 12)
      (by rw [show (4 * 67 : Nat) = 268 from rfl, BitVec.add_assoc]
          rfl)
      (by omega) rfl)
    (by rw [show signExtend21 (128 : BitVec 21) = (128 : Word) from
          by decide,
        BitVec.add_assoc, BitVec.add_assoc]
        rfl)
    hcsB hw hlenS
  rwa [show (EddB + 256) + 16 = EddB + 272 from by
    rw [BitVec.add_assoc]; rfl] at hg
set_option maxRecDepth 400000 in
/-- ⭐ **The ok path of `extract_deposit_data` at its linked guest
    address** (#12989): entered with `a0` = the 576-byte DepositEvent
    payload arena (`eddDataPtr`), `a1 = 576`, `a2` = the 192-byte output
    arena (`eddOutPtr`), three owned frame dwords below `sp`, and a
    payload whose ten ABI header fields all satisfy `eddOk`, it copies
    the five raw fields into the output arena and returns `a0 = 0` with
    `sp`/`ra`/`s0`/`s1` restored.  Composed over the shared three-entry
    bundle image; the ten checks and five copies are the verified DCode
    leaves, linked by `callWithin_spec`. -/
theorem extractDepositData_ok_spec
    (sp0 ret v5 v8 v9 m0 m1 m2 : Word)
    (b0 b32 b64 b96 b128 b160 b256 b320 b384 b512 : List (BitVec 8))
    (s192 s288 s352 s416 s544 : List (BitVec 8))
    (w0 w48 w80 w88 w184 : List (BitVec 8))
    (hb0 : b0.length = 32) (hb32 : b32.length = 32)
    (hb64 : b64.length = 32) (hb96 : b96.length = 32)
    (hb128 : b128.length = 32) (hb160 : b160.length = 32)
    (hb256 : b256.length = 32) (hb320 : b320.length = 32)
    (hb384 : b384.length = 32) (hb512 : b512.length = 32)
    (hs192 : s192.length = 48) (hs288 : s288.length = 32)
    (hs352 : s352.length = 8) (hs416 : s416.length = 96)
    (hs544 : s544.length = 8)
    (hw0 : w0.length = 48) (hw48 : w48.length = 32)
    (hw80 : w80.length = 8) (hw88 : w88.length = 96)
    (hw184 : w184.length = 8)
    (hok0 : EddBe32EqSAsm.eddOk eddDataPtr b0 (160 : Word))
    (hok32 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 32) b32 (256 : Word))
    (hok64 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 64) b64 (320 : Word))
    (hok96 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 96) b96 (384 : Word))
    (hok128 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 128) b128 (512 : Word))
    (hok160 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 160) b160 (48 : Word))
    (hok256 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 256) b256 (32 : Word))
    (hok320 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 320) b320 (8 : Word))
    (hok384 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 384) b384 (96 : Word))
    (hok512 : EddBe32EqSAsm.eddOk (eddDataPtr + BitVec.ofNat 64 512) b512 (8 : Word))
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7749 EddB (ret &&& ~~~1) eddbCode
      (((.x2 : Reg) ↦ᵣ sp0) **
        ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) **
        ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ eddDataPtr) **
        ((.x11 : Reg) ↦ᵣ (576 : Word)) **
        ((.x12 : Reg) ↦ᵣ eddOutPtr) **
        ((.x5 : Reg) ↦ᵣ v5) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns eddScrPre **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ m0) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ m1) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ m2) **
        bytesRegion eddDataPtr b0 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
        bytesRegion eddOutPtr w0 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
      (((.x2 : Reg) ↦ᵣ sp0) **
        ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) **
        ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns eddScr14 **
        ((sp0 + signExtend12 (-32 : BitVec 12)) ↦ₘ ret) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 8) ↦ₘ v8) **
        ((sp0 + signExtend12 (-32 : BitVec 12) + 16) ↦ₘ v9) **
        bytesRegion eddDataPtr b0 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
        bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
        bytesRegion eddOutPtr s192 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 88) s416 **
        bytesRegion (eddOutPtr + BitVec.ofNat 64 184) s544) := by
  set nsp := sp0 + signExtend12 (-32 : BitVec 12) with hnsp
  -- ---- idx 0-6: frame prologue ----
  have haddisp := addi_spec_gen_same_within .x2 sp0 (-32 : BitVec 12)
    EddB (by decide)
  rw [← hnsp] at haddisp
  have hsd1 := sd_spec_gen_within .x2 .x1 nsp ret m0 (0 : BitVec 12) (EddB + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show nsp + (0 : Word) = nsp from by bv_omega] at hsd1
  have hsd2 := sd_spec_gen_within .x2 .x8 nsp v8 m1 (8 : BitVec 12) (EddB + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hsd2
  have hsd3 := sd_spec_gen_within .x2 .x9 nsp v9 m2 (16 : BitVec 12) (EddB + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at hsd3
  have hmv8 := mv_spec_gen_within .x8 .x10 eddDataPtr v8 (EddB + 16) (by decide)
  have hmv9 := mv_spec_gen_within .x9 .x12 eddOutPtr v9 (EddB + 20) (by decide)
  have hli5 := li_spec_gen_within .x5 v5 (576 : Word) (EddB + 24) (by decide)
  have hProl : cpsTripleWithin 7 EddB (EddB + 28) eddbCode
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        ((.x10 : Reg) ↦ᵣ eddDataPtr) ** ((.x12 : Reg) ↦ᵣ eddOutPtr) **
        ((.x5 : Reg) ↦ᵣ v5) **
        (nsp ↦ₘ m0) ** ((nsp + 8) ↦ₘ m1) ** ((nsp + 16) ↦ₘ m2))
      (((.x2 : Reg) ↦ᵣ nsp) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr) **
        ((.x10 : Reg) ↦ᵣ eddDataPtr) ** ((.x12 : Reg) ↦ᵣ eddOutPtr) **
        ((.x5 : Reg) ↦ᵣ (576 : Word)) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9)) := by
    runBlock haddisp hsd1 hsd2 hsd3 hmv8 hmv9 hli5
  -- ---- idx 7: bne a1, t0 NOT taken (a1 = 576) ----
  have hbne := bne_spec_gen_within .x11 .x5 (252 : BitVec 13) (576 : Word)
    (576 : Word) (EddB + 28)
  have hBne := cpsTripleWithin_extend_code
    (eddb_mem 7 _ (EddB + 28)
      (by rw [show (4 * 7 : Nat) = 28 from rfl]; rfl) (by omega) rfl)
    (cpsBranchWithin_ntakenPath hbne
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2)))
  rw [show (EddB + 28 : Word) + 4 = EddB + 32 from by
    rw [BitVec.add_assoc]; rfl] at hBne
  have hg1F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g1 b0 (by omega) (by
      have h := EvmAsm.Codegen.edd_src_region_wf 0 32 b0 hb0 rfl (by omega)
      rwa [show eddDataPtr + BitVec.ofNat 64 0 = eddDataPtr from by decide]
        at h) hok0)
  have hg2F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g2 b32 (by omega) (EvmAsm.Codegen.edd_src_region_wf 32 32 b32 hb32 rfl (by omega)) hok32)
  have hg3F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g3 b64 (by omega) (EvmAsm.Codegen.edd_src_region_wf 64 32 b64 hb64 rfl (by omega)) hok64)
  have hg4F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g4 b96 (by omega) (EvmAsm.Codegen.edd_src_region_wf 96 32 b96 hb96 rfl (by omega)) hok96)
  have hg5F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g5 b128 (by omega) (EvmAsm.Codegen.edd_src_region_wf 128 32 b128 hb128 rfl (by omega)) hok128)
  have hg6F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g6 b160 (by omega) (EvmAsm.Codegen.edd_src_region_wf 160 32 b160 hb160 rfl (by omega)) hok160)
  have hg7F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g7 b256 (by omega) (EvmAsm.Codegen.edd_src_region_wf 256 32 b256 hb256 rfl (by omega)) hok256)
  have hg8F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g8 b320 (by omega) (EvmAsm.Codegen.edd_src_region_wf 320 32 b320 hb320 rfl (by omega)) hok320)
  have hg9F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g9 b384 (by omega) (EvmAsm.Codegen.edd_src_region_wf 384 32 b384 hb384 rfl (by omega)) hok384)
  have hg10F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_check_g10 b512 (by omega) (EvmAsm.Codegen.edd_src_region_wf 512 32 b512 hb512 rfl (by omega)) hok512)
  have hc1F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_copy_c1 s192 w0 hs192 hw0)
  have hc2F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr s192 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_copy_c2 s288 w48 hs288 hw48)
  have hc3F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr s192 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_copy_c3 s352 w80 hs352 hw80)
  have hc4F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr s192 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree)
    (edd_copy_c4 s416 w88 hs416 hw88)
  have hc5F := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion eddOutPtr s192 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) s416)
    (by edd_pcfree)
    (edd_copy_c5 s544 w184 hs544 hw184)
  -- ---- idx 68: li a0, 0 ----
  have hli0 := li_spec_gen_own_within .x10 (0 : Word) (EddB + 272) (by decide)
  have hLi0 := cpsTripleWithin_extend_code
    (eddb_mem 68 _ (EddB + 272)
      (by rw [show (4 * 68 : Nat) = 272 from rfl]; rfl) (by omega) rfl) hli0
  rw [show (EddB + 272 : Word) + 4 = EddB + 276 from by
    rw [BitVec.add_assoc]; rfl] at hLi0
  have hLi0F := cpsTripleWithin_frameR
    (regOwn .x1 **
      ((.x2 : Reg) ↦ᵣ nsp) **
      ((.x8 : Reg) ↦ᵣ eddDataPtr) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwns eddScr14 **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr s192 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) s416 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) s544)
    (by edd_pcfree) hLi0
  -- ---- idx 69: jal x0, +8 (skip the fail tail) ----
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (EddB + 276)
  rw [show (EddB + 276 : Word) + signExtend21 (8 : BitVec 21) = EddB + 284
    from by
      rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide,
        BitVec.add_assoc]
      rfl] at hjal
  have hJal := cpsTripleWithin_extend_code
    (eddb_mem 69 _ (EddB + 276)
      (by rw [show (4 * 69 : Nat) = 276 from rfl]; rfl) (by omega) rfl) hjal
  have hJalF := cpsTripleWithin_frameR
    (regOwn .x1 **
      ((.x2 : Reg) ↦ᵣ nsp) **
      ((.x8 : Reg) ↦ᵣ eddDataPtr) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      regOwns eddScr14 **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr s192 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) s416 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) s544)
    (by edd_pcfree) hJal
  -- ---- idx 71-75: epilogue ----
  have hEpi : cpsTripleWithin 5 (EddB + 284) (ret &&& ~~~1) eddbCode
      (regOwn .x1 ** ((.x2 : Reg) ↦ᵣ nsp) **
        ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9))
      (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
        (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9)) := by
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq)
      (cpsTripleWithin_of_forall_regIs_to_regOwn
        (P := ((.x2 : Reg) ↦ᵣ nsp) **
          ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr) **
          (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9))
        (fun v1 => ?_))
    have hld1 := ld_spec_gen_within .x1 .x2 nsp v1 ret (0 : BitVec 12)
      (EddB + 284) (by decide)
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show nsp + (0 : Word) = nsp from by bv_omega] at hld1
    have hld8 := ld_spec_gen_within .x8 .x2 nsp eddDataPtr v8 (8 : BitVec 12)
      (EddB + 288) (by decide)
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hld8
    have hld9 := ld_spec_gen_within .x9 .x2 nsp eddOutPtr v9 (16 : BitVec 12)
      (EddB + 292) (by decide)
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
      at hld9
    have haddisp2 := addi_spec_gen_same_within .x2 nsp (32 : BitVec 12)
      (EddB + 296) (by decide)
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
        show nsp + (32 : Word) = sp0 from by
          rw [hnsp, show signExtend12 (-32 : BitVec 12)
            = (0xFFFFFFFFFFFFFFE0 : Word) from by decide]
          bv_omega] at haddisp2
    have hret2 := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (EddB + 300)
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
        show (ret + 0 : Word) = ret from by bv_omega] at hret2
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq)
      (?_ : cpsTripleWithin 5 (EddB + 284) (ret &&& ~~~1) eddbCode
        (((.x2 : Reg) ↦ᵣ nsp) ** ((.x1 : Reg) ↦ᵣ v1) **
          ((.x8 : Reg) ↦ᵣ eddDataPtr) ** ((.x9 : Reg) ↦ᵣ eddOutPtr) **
          (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9))
        (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ ret) **
          ((.x8 : Reg) ↦ᵣ v8) ** ((.x9 : Reg) ↦ᵣ v9) **
          (nsp ↦ₘ ret) ** ((nsp + 8) ↦ₘ v8) ** ((nsp + 16) ↦ₘ v9)))
    runBlock hld1 hld8 hld9 haddisp2 hret2
  have hEpiF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwns eddScr14 **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr s192 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) s416 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) s544)
    (by edd_pcfree) hEpi
  have hProlF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ (576 : Word)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwns eddScrPre **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree) hProl
  have hBneF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ nsp) **
      ((.x1 : Reg) ↦ᵣ ret) **
      ((.x8 : Reg) ↦ᵣ eddDataPtr) **
      ((.x9 : Reg) ↦ᵣ eddOutPtr) **
      ((.x10 : Reg) ↦ᵣ eddDataPtr) **
      ((.x12 : Reg) ↦ᵣ eddOutPtr) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwns eddScrPre **
      (nsp ↦ₘ ret) **
      ((nsp + 8) ↦ₘ v8) **
      ((nsp + 16) ↦ₘ v9) **
      bytesRegion eddDataPtr b0 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
      bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
      bytesRegion eddOutPtr w0 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
      bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)
    (by edd_pcfree) hBne
  -- ---- chain ----
  have t0 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hProlF hBneF
    intro h hp; xperm_hyp hp
  have t1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t0 hg1F
    intro h hp
    have hp1 : (((((.x5 : Reg) ↦ᵣ (576 : Word)) **
        ((.x10 : Reg) ↦ᵣ eddDataPtr) ** ((.x11 : Reg) ↦ᵣ (576 : Word)) **
        ((.x12 : Reg) ↦ᵣ eddOutPtr)) ** regOwns eddScrPre) **
        (((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ nsp) **
          ((.x8 : Reg) ↦ᵣ eddDataPtr) **
          ((.x9 : Reg) ↦ᵣ eddOutPtr) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (nsp ↦ₘ ret) **
          ((nsp + 8) ↦ₘ v8) **
          ((nsp + 16) ↦ₘ v9) **
          bytesRegion eddDataPtr b0 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
          bytesRegion eddOutPtr w0 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 48) w48 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 80) w80 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 88) w88 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 184) w184)) h := by
      have hp0 := sepConj_mono_left (sepConj_mono_right
        (fun h' hx => ((sepConj_pure_right h').1 hx).1)) h hp
      xperm_hyp hp0
    have hp2 := sepConj_mono_left
      (fun h' hx => edd_owns_assemble h'
        (sepConj_mono_left
          (fun h'' hy =>
            sepConj_mono (regIs_to_regOwn .x5 (576 : Word))
              (sepConj_mono (regIs_to_regOwn .x10 eddDataPtr)
                (sepConj_mono (regIs_to_regOwn .x11 (576 : Word))
                  (regIs_to_regOwn .x12 eddOutPtr))) h'' hy)
          h' hx))
      h hp1
    have hp3 := sepConj_mono_right (sepConj_mono_left
      (regIs_to_regOwn .x1 ret)) h hp2
    xperm_hyp hp3
  have t2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t1 hg2F
    intro h hp; xperm_hyp hp
  have t3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t2 hg3F
    intro h hp; xperm_hyp hp
  have t4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t3 hg4F
    intro h hp; xperm_hyp hp
  have t5 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t4 hg5F
    intro h hp; xperm_hyp hp
  have t6 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t5 hg6F
    intro h hp; xperm_hyp hp
  have t7 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t6 hg7F
    intro h hp; xperm_hyp hp
  have t8 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t7 hg8F
    intro h hp; xperm_hyp hp
  have t9 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t8 hg9F
    intro h hp; xperm_hyp hp
  have t10 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t9 hg10F
    intro h hp; xperm_hyp hp
  have t11 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t10 hc1F
    intro h hp; xperm_hyp hp
  have t12 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t11 hc2F
    intro h hp; xperm_hyp hp
  have t13 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t12 hc3F
    intro h hp; xperm_hyp hp
  have t14 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t13 hc4F
    intro h hp; xperm_hyp hp
  have t15 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t14 hc5F
    intro h hp; xperm_hyp hp
  have tLi := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t15 hLi0F
    intro h hp
    have hp1 := sepConj_mono_left edd_owns_split h
      (by xperm_hyp hp :
        (regOwns exposedRegs ** (regOwn .x1 ** ((.x2 : Reg) ↦ᵣ nsp) **
          ((.x8 : Reg) ↦ᵣ eddDataPtr) **
          ((.x9 : Reg) ↦ᵣ eddOutPtr) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (nsp ↦ₘ ret) **
          ((nsp + 8) ↦ₘ v8) **
          ((nsp + 16) ↦ₘ v9) **
          bytesRegion eddDataPtr b0 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
          bytesRegion eddOutPtr s192 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 88) s416 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 184) s544)) h)
    xperm_hyp hp1
  have tJal := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ tLi hJalF
    intro h hp
    have hp1 : (empAssertion ** (regOwn .x1 ** ((.x2 : Reg) ↦ᵣ nsp) **
          ((.x8 : Reg) ↦ᵣ eddDataPtr) **
          ((.x9 : Reg) ↦ᵣ eddOutPtr) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) **
          regOwns eddScr14 **
          (nsp ↦ₘ ret) **
          ((nsp + 8) ↦ₘ v8) **
          ((nsp + 16) ↦ₘ v9) **
          bytesRegion eddDataPtr b0 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 32) b32 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 64) b64 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 96) b96 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 128) b128 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 160) b160 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 256) b256 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 320) b320 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 384) b384 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 512) b512 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 192) s192 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 288) s288 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 352) s352 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 416) s416 **
          bytesRegion (eddDataPtr + BitVec.ofNat 64 544) s544 **
          bytesRegion eddOutPtr s192 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 48) s288 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 80) s352 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 88) s416 **
          bytesRegion (eddOutPtr + BitVec.ofNat 64 184) s544)) h := by
      rw [sepConj_emp_left']
      xperm_hyp hp
    exact hp1
  have tEpi := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ tJal hEpiF
    intro h hp
    have hp1 : (empAssertion ** _) h := hp
    rw [sepConj_emp_left'] at hp1
    xperm_hyp hp1
  refine cps_fuel_mono (by norm_num)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq) tEpi)

end EvmAsm.Codegen.ExtractDepositDataOkSpec
