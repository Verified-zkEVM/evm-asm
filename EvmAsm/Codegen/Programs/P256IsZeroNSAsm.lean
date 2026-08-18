/-
  EvmAsm.Codegen.Programs.P256IsZeroNSAsm

  Verified SAsm drop-in for `p256_is_zero_n`: dynamic-length byte-zero scan.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Rv64.SAsm.WhileBreakDemo
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.SAsm.Stmt
open EvmAsm.Rv64.SAsm.WhileBreakDemo

namespace P256IsZeroNSAsm

/-- Result for the first `len` bytes of `bs`: 1 iff every scanned byte is zero. -/
def isZeroNResult (bs : List (BitVec 8)) (len : Nat) : Word :=
  if nlz bs len = len then (1 : Word) else (0 : Word)

/-- Loop post enriched with the static facts needed by the public `Fn.post`. -/
def p256IsZeroNScanPost (ptr : Word) (bs : List (BitVec 8)) (len : Nat) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ A =>
    rf.get .x5 = ptr + BitVec.ofNat 64 (nlz bs len) ∧
    rf.get .x6 = BitVec.ofNat 64 (len - nlz bs len) ∧
    len ≤ bs.length ∧ ptr.toNat + len < 2 ^ 64 ∧ A = empAssertion

/-- Scan `a0[0..a1)` for a nonzero byte, then return 1 iff none was found. -/
def p256IsZeroNBody (ptr : Word) (bs : List (BitVec 8)) (len : Nat) : Stmt :=
  .block "init" [.MV .x5 .x10, .MV .x6 .x11] ;;;
  .«whileBreak» "scan" (.bne .x6 .x0) len
    (scanInv ptr bs len) (p256IsZeroNScanPost ptr bs len)
    (.block "load" [.LBU .x7 .x5 (0 : BitVec 12)]) (.bne .x7 .x0)
    (.block "next" [.ADDI .x5 .x5 (1 : BitVec 12), .ADDI .x6 .x6 (-1 : BitVec 12)]) ;;;
  .block "res1" [.LI .x10 (1 : Word)] ;;;
  .when "clr" (.bne .x6 .x0) (.block "clr0" [.LI .x10 (0 : Word)])

/-- Verified `Fn`: `x10 := 1` iff the first `len` bytes at `ptr` are all zero. -/
def p256IsZeroNFn (ptr : Word) (bs : List (BitVec 8)) (len : Nat) : Fn where
  name := "p256IsZeroN"
  region := ⟨ptr, bs⟩
  -- ⚠️ Ambient PINNED (#12244) so the flat lift's `hpostEmp` can be discharged; the
  -- shared `scanInv` is pinned to match, since the fact must cross the loop boundary.
  pre := fun rf _ A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = BitVec.ofNat 64 len ∧
    len ≤ bs.length ∧ ptr.toNat + len < 2 ^ 64 ∧ A = empAssertion
  post := fun rf _ A =>
    rf.get .x10 = isZeroNResult bs len ∧ len ≤ bs.length ∧
      ptr.toNat + len < 2 ^ 64 ∧ A = empAssertion
  body := p256IsZeroNBody ptr bs len

/-- Re-emitted drop-in: verified single-exit body plus `ret`. -/
def p256IsZeroN_prog : Program :=
  (p256IsZeroNBody 0 [] 0).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

def p256IsZeroNFunction : String :=
  "p256_is_zero_n:\n" ++ emitProgram p256IsZeroN_prog

theorem p256IsZeroNFunction_eq_prog :
    p256IsZeroNFunction = "p256_is_zero_n:\n" ++ emitProgram p256IsZeroN_prog := rfl

#guard p256IsZeroNFunction.startsWith "p256_is_zero_n:\n"
#guard p256IsZeroN_prog.length = 12
#guard (p256IsZeroNBody 0 [] 0).flatten 0 =
  (p256IsZeroNBody 0 [] 0).flatten 0x80000000

theorem p256IsZeroNFn_spec (ptr : Word) (bs : List (BitVec 8)) (len : Nat)
    (hwf : (Region.mk ptr bs).wf) (base : Word) :
    (p256IsZeroNFn ptr bs len).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case p256IsZeroN.scan.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11, hlen, hptr⟩, rfl, rfl⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws₀
    simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem]
    refine ⟨?_, ?_, Nat.zero_le _, hlen, hptr⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide), hx10]
      simp
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
      simp
  case p256IsZeroN.scan.inv_step =>
    rintro i hi rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, hnbreak⟩, hrf', -⟩ := hsp
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrfa, -⟩ := hspbb
    obtain ⟨hx5, hx6, hle, hlen, hptr⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hilt : i < len := by
      rcases Nat.lt_or_ge i len with h | h
      · exact h
      · exfalso; apply hg
        show rfb.get .x6 = rfb.get .x0
        rw [hx6, show len - i = 0 from by omega]; rfl
    have hbyte : (p256IsZeroNFn ptr bs len).region.byteAt (rfb.get .x5 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (p256IsZeroNFn ptr bs len).region.bytes = bs from rfl,
          show (p256IsZeroNFn ptr bs len).region.base = ptr from rfl, hx5, hse0]
      congr 1
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hrfa5 : rfa.get .x5 = rfb.get .x5 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]
    have hrfa6 : rfa.get .x6 = rfb.get .x6 := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    have hrfa7 : rfa.get .x7 = BitVec.zeroExtend 64 (bs.getD i 0) := by
      rw [hrfa]
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0)]
      rw [hbyte]
    have hz : bs.getD i 0 = 0 := by
      have hne : rfa.get .x7 = rfa.get .x0 := by
        by_contra h; exact hnbreak h
      rw [hrfa7, show rfa.get .x0 = 0 from rfl] at hne
      bv_omega
    refine ⟨?_, ?_, nlz_continue bs len i hilt hlen hz hle, hlen, hptr⟩
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide : (Reg.x5 : Reg) ≠ .x0)]
      rw [hrfa5, hx5, hse1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x6 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5)]
      rw [hrfa6, hx6, hsem1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
  case p256IsZeroN.scan.exhausted =>
    rintro rf ws A ⟨-, hx6, -, -, -⟩
    intro hc
    apply hc
    rw [hx6, show len - len = 0 from by omega]; rfl
  case p256IsZeroN.scan.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hle, hlen, hptr⟩ hng
    have hil : i = len := by
      by_contra hne
      apply hng
      show rf.get .x6 ≠ rf.get .x0
      rw [hx6, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
      omega
    have hnlz : nlz bs len = len := by
      have := nlz_le bs len; omega
    refine ⟨?_, ?_, hlen, hptr⟩
    · rw [hx5, hnlz, hil]
    · rw [hx6, hnlz, hil]
  case p256IsZeroN.scan.break =>
    rintro i hi rf' ws' A' hsp hbreak
    obtain ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf', -⟩ := hsp
    obtain ⟨hx5, hx6, hle, hlen, hptr⟩ := hinv
    obtain rfl := List.eq_nil_of_length_eq_zero hwsb
    have hbyte : (p256IsZeroNFn ptr bs len).region.byteAt (rfb.get .x5 + signExtend12 0)
        = bs.getD i 0 := by
      unfold Region.byteAt
      rw [show (p256IsZeroNFn ptr bs len).region.bytes = bs from rfl,
          show (p256IsZeroNFn ptr bs len).region.base = ptr from rfl, hx5, hse0]
      congr 1
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hrf7 : rf'.get .x7 = BitVec.zeroExtend 64 (bs.getD i 0) := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0)]
      rw [hbyte]
    have hrf5 : rf'.get .x5 = rfb.get .x5 := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]
    have hrf6 : rf'.get .x6 = rfb.get .x6 := by
      rw [hrf']
      simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem, loadSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    have hnz : bs.getD i 0 ≠ 0 := by
      have hne : rf'.get .x7 ≠ rf'.get .x0 := hbreak
      rw [hrf7, show rf'.get .x0 = 0 from rfl] at hne
      intro hz
      exact hne (by rw [hz]; rfl)
    have hieq : i = nlz bs len := nlz_break bs len i hle hnz
    refine ⟨?_, ?_, hlen, hptr⟩
    · rw [hrf5, hx5, hieq]
    · rw [hrf6, hx6, hieq]
  case p256IsZeroN.scan.before.load.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hle, hlen, hptr⟩, hg⟩
    obtain rfl := List.eq_nil_of_length_eq_zero hws
    have hilt : i < len := by
      rcases Nat.lt_or_ge i len with h | h
      · exact h
      · exfalso; apply hg
        rw [hx6, show len - i = 0 from by omega]; rfl
    simp only [blockVCs, loadSem]
    refine ⟨⟨one_dvd _, ?_⟩, trivial⟩
    show ((rf.get .x5 + signExtend12 (0 : BitVec 12)) - ptr).toNat + 1 ≤ bs.length
    rw [hse0, hx5]
    have haddr : ((ptr + BitVec.ofNat 64 i + 0) - ptr).toNat = i := by bv_omega
    rw [haddr]; omega
  case p256IsZeroN.post =>
    rintro rf ws A hpost
    rcases hpost with
      ⟨rf₁, ws₁, hws₁, ⟨hres1, hcond⟩, hrf1, rfl⟩ | ⟨hres1, hnc⟩
    · obtain rfl := List.eq_nil_of_length_eq_zero hws₁
      obtain ⟨rfa, wsa, hwsa, hscanPost, hrf1eq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨-, hx6a, hlen, hptr⟩ := hscanPost
      have hx10rf : rf.get .x10 = (0 : Word) := by
        rw [hrf1]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hr1x6 : rf₁.get .x6 = rfa.get .x6 := by
        rw [hrf1eq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x10)]
      have hne : nlz bs len ≠ len := by
        dsimp only [Cond.holds] at hcond
        intro heq
        apply hcond
        rw [hr1x6, hx6a, heq]
        simp
      refine ⟨?_, hlen, hptr⟩
      rw [hx10rf, isZeroNResult, if_neg hne]
    · obtain ⟨rfa, wsa, hwsa, hscanPost, hrfeq, -⟩ := hres1
      obtain rfl := List.eq_nil_of_length_eq_zero hwsa
      obtain ⟨-, hx6a, hlen, hptr⟩ := hscanPost
      have hx10rf : rf.get .x10 = (1 : Word) := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_self _ _ _ (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have hrfx6 : rf.get .x6 = rfa.get .x6 := by
        rw [hrfeq]
        simp only [execBlock_cons, execBlock_nil, execInstrRF_nil, aluSem,
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x10)]
      dsimp only [Cond.holds] at hnc
      have heq : nlz bs len = len := by
        have h0 : rf.get .x6 = (0 : Word) := by
          by_contra hne
          exact hnc hne
        have hx6post : rf.get .x6 = BitVec.ofNat 64 (len - nlz bs len) := by
          rw [hrfx6, hx6a]
        rw [hx6post] at h0
        have hle : nlz bs len ≤ len := nlz_le bs len
        have hdiff_lt : len - nlz bs len < 2 ^ 64 := by omega
        have := congrArg (fun w : Word => w.toNat) h0
        simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this
        rw [Nat.mod_eq_of_lt hdiff_lt] at this
        omega
      refine ⟨?_, hlen, hptr⟩
      rw [hx10rf, isZeroNResult, if_pos heq]


/-! ## Flat linked-entry contract (#12244)

    Anchored over `CodeReq.ofProg (GuestAddrs.p256_is_zero_n) p256IsZeroN_prog` — the
    `GuestImageEntries` pairing — so this is a statement about the DEPLOYED image.

    Geometry is the is-zero mirror: non-empty read-only `region` riding through as the
    trailing conjunct, EMPTY writable `rw` (`ws = []`).  Memory is UNTOUCHED — the scanned
    region is pinned intact in the post, and the only state change is `a0`.

    ⚠️ Asymmetric registers, so two splits: the pre pins `a0` (pointer) and `a1` (length)
    while the post publishes only `a0`, the result.  Total over its argument types given
    the ABI hypotheses (`len ≤ bs.length`, no address wraparound, region wf, aligned `ra`)
    — no input-domain restriction.

    ⭐ The blocker here was the SHARED `WhileBreakDemo.scanInv`, and the measured blast
    radius turned out to be two consumers (the demo itself and this routine), not
    "`Rv64/SAsm` infrastructure": every other external use of that module is of the pure
    `nlz` spec function, not the invariant.  Pinning it cost four edits in the demo. -/

def p256IsZeroNCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.p256_is_zero_n : Word) p256IsZeroN_prog

/-- Exposed registers excluding the two ABI argument registers. -/
def p256ArgScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Exposed registers excluding only the result register `a0`. -/
def p256ResScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_p256_2 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf p256ArgScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [p256ArgScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem exposedRegs_split_p256_1 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf p256ResScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [p256ResScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_p256ArgScratch : (.x10 : Reg) ∉ p256ArgScratch := by decide
private theorem x11_notin_p256ArgScratch : (.x11 : Reg) ∉ p256ArgScratch := by decide

/-- **`p256_is_zero_n`, whole-routine flat triple at the guest entry.**

    `a0` becomes `isZeroNResult bs len` — `1` iff the first `len` bytes at the pointer are
    all zero, else `0`. The scanned region is pinned INTACT. -/
theorem p256IsZeroNFlat_spec (ret ptr : Word) (bs : List (BitVec 8)) (len : Nat)
    (hwf : (Region.mk ptr bs).wf) (hlen : len ≤ bs.length)
    (hptr : ptr.toNat + len < 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((p256IsZeroNFn ptr bs len).body.steps + 1)
      (GuestAddrs.p256_is_zero_n : Word) ret p256IsZeroNCr
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
        regOwns p256ArgScratch ** bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ isZeroNResult bs len) **
        regOwns p256ResScratch ** bytesRegion ptr bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns p256ArgScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** bytesRegion ptr bs)
      (fun vf => ?_))
  have hpre : (p256IsZeroNFn ptr bs len).pre
      (fun r => if r = .x10 then ptr else if r = .x11 then BitVec.ofNat 64 len
        else vf r) [] empAssertion := by
    refine ⟨?_, ?_, hlen, hptr, rfl⟩
    · show RegFile.get _ .x10 = ptr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = BitVec.ofNat 64 len
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0),
        if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlat (p256IsZeroNFn ptr bs len)
    (GuestAddrs.p256_is_zero_n : Word)
    (p256IsZeroNFn_spec ptr bs len hwf (GuestAddrs.p256_is_zero_n : Word))
    -- 11 = the flattened body length; `p256IsZeroN_prog` is 12 with its ret (`#guard`).
    (by show 4 * (11 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then ptr else if r = .x11 then BitVec.ofNat 64 len
      else vf r)
    [] rfl hpre
    (Q := ((.x10 : Reg) ↦ᵣ isZeroNResult bs len) ** regOwns p256ResScratch)
    -- `hpostEmp`: the ambient is pinned by the `Fn` post's fourth conjunct.
    (fun _ _ _ hpost => hpost.2.2.2)
    (fun rf' ws' hlenWs hpost hp hh => by
      obtain ⟨hx10, -, -, -⟩ := hpost
      obtain rfl : ws' = [] := List.eq_nil_of_length_eq_zero hlenWs
      simp only [bytesRegion_nil, sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_p256_1,
        show rf' .x10 = isZeroNResult bs len from by
          rw [← hx10, RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]] at hh
      exact sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) p256ResScratch) hp hh)
  rw [show (p256IsZeroNFn ptr bs len).programRet
      (GuestAddrs.p256_is_zero_n : Word) = p256IsZeroN_prog from rfl] at had
  rw [show (p256IsZeroNFn ptr bs len).rw.base = (0 : Word) from rfl,
    show (p256IsZeroNFn ptr bs len).region.base = ptr from rfl,
    show (p256IsZeroNFn ptr bs len).region.bytes = bs from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_p256_2,
    show (if (Reg.x10 : Reg) = .x10 then ptr else
        if (Reg.x10 : Reg) = .x11 then BitVec.ofNat 64 len else vf .x10)
      = ptr from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then ptr else
        if (Reg.x11 : Reg) = .x11 then BitVec.ofNat 64 len else vf .x11)
      = BitVec.ofNat 64 len from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then ptr else if r = .x11 then BitVec.ofNat 64 len
        else vf r)
      vf p256ArgScratch
      (fun r hr => by
        show (if r = .x10 then ptr else if r = .x11 then BitVec.ofNat 64 len
          else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_p256ArgScratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_p256ArgScratch (hc ▸ hr))])] at had
  simp only [bytesRegion_nil, sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end P256IsZeroNSAsm
end EvmAsm.Codegen
