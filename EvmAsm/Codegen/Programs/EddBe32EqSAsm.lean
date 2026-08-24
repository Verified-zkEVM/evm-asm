/-
  EvmAsm.Codegen.Programs.EddBe32EqSAsm

  Proof-first (DCode) port of `edd_be32_eq` — the deposit-request
  extractor's 32-byte big-endian u32 comparator (`a0` = pointer to a
  32-byte BE field, `a1` = the expected value; returns `a0 = 1` iff the
  high 28 bytes are zero and the low 4 bytes assemble to `a1`).

  First user of the header-reloaded return-terminating break loop
  (`dretWhileHeaderBreak` / `Stmt.retWhileHeaderBreak`): the zero-scan's
  header reloads `li t1, 28` every trip, its break (a nonzero high byte)
  and the final compare guard both return through ONE shared `ne` tail —
  the loop break entering the following cascade's bad tail, a layout no
  composition of the existing nodes can express.  Byte-identity with the
  hand-written routine in `ExtractDepositData.lean` verified by
  assemble+cmp; the emitted slice is now `emitProgram` of the generated
  program.
-/

import EvmAsm.Rv64.SAsm.Deriv

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

namespace EddBe32EqSAsm

/-! ## The routine's semantics -/

/-- Byte `j` of the field, zero-extended (what `lbu` loads). -/
def eddB (ptr : Word) (bs : List (BitVec 8)) (j : Nat) : Word :=
  BitVec.zeroExtend 64
    ((Region.mk ptr bs).byteAt (ptr + BitVec.ofNat 64 j))

/-- The machine's big-endian u32 assembly of bytes 28..31. -/
def eddU32 (ptr : Word) (bs : List (BitVec 8)) : Word :=
  ((eddB ptr bs 28 <<< (24 : Nat) ||| eddB ptr bs 29 <<< (16 : Nat))
    ||| eddB ptr bs 30 <<< (8 : Nat)) ||| eddB ptr bs 31

/-- The comparator's acceptance condition. -/
def eddOk (ptr : Word) (bs : List (BitVec 8)) (K : Word) : Prop :=
  (∀ j, j < 28 → eddB ptr bs j = 0) ∧ eddU32 ptr bs = K

instance (ptr : Word) (bs : List (BitVec 8)) (K : Word) :
    Decidable (eddOk ptr bs K) := by
  unfold eddOk
  infer_instance

/-- The returned flag. -/
def eddOut (ptr : Word) (bs : List (BitVec 8)) (K : Word) : Word :=
  if eddOk ptr bs K then 1 else 0

/-- Facts the routine never disturbs. -/
def eddStatic (ptr : Word) (bs : List (BitVec 8)) (K : Word)
    (rf : RegFile) : Prop :=
  rf.get .x10 = ptr ∧ rf.get .x11 = K ∧ 32 ≤ bs.length

/-- Zero-scan invariant at the i-th guard evaluation (after the header). -/
def eddInv (ptr : Word) (bs : List (BitVec 8)) (K : Word) : Nat → Reach :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧ rf.get .x6 = (28 : Word) ∧ i ≤ 28 ∧
    (∀ j, j < i → eddB ptr bs j = 0) ∧ eddStatic ptr bs K rf ∧
    A = empAssertion

/-- Mid-states at the break test: `t3` holds byte `i`. -/
def eddMid (ptr : Word) (bs : List (BitVec 8)) (K : Word) : Nat → Reach :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧ i < 28 ∧
    rf.get .x28 = eddB ptr bs i ∧
    (∀ j, j < i → eddB ptr bs j = 0) ∧ eddStatic ptr bs K rf ∧
    A = empAssertion

/-- States after the counter bump (the header re-runs from here). -/
def eddEnd (ptr : Word) (bs : List (BitVec 8)) (K : Word) : Nat → Reach :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 (i + 1) ∧ i < 28 ∧
    (∀ j, j < i + 1 → eddB ptr bs j = 0) ∧ eddStatic ptr bs K rf ∧
    A = empAssertion

/-- Cascade invariant: entry = the zero-scan passed; after the compare
    stage = fully accepted. -/
def eddCinv (ptr : Word) (bs : List (BitVec 8)) (K : Word) : Nat → Reach
  | 0 => fun rf _ A =>
      (∀ j, j < 28 → eddB ptr bs j = 0) ∧ eddStatic ptr bs K rf ∧
      A = empAssertion
  | _ + 1 => fun _ _ A => eddOk ptr bs K ∧ A = empAssertion

/-- Shared bad-entry states. -/
def eddBad (ptr : Word) (bs : List (BitVec 8)) (K : Word) : Reach :=
  fun _ _ A => ¬ eddOk ptr bs K ∧ A = empAssertion

/-! ## Local machine-step helpers (all at the empty writable window) -/

theorem execInstrRF_li' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd : Reg) (v : Word) :
    execInstrRF ro b rf ws (.LI rd v) = (rf.set rd v, ws) := rfl

theorem execInstrRF_add' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 rs2 : Reg) :
    execInstrRF ro b rf ws (.ADD rd rs1 rs2)
      = (rf.set rd (rf.get rs1 + rf.get rs2), ws) := rfl

theorem execInstrRF_addi' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrRF ro b rf ws (.ADDI rd rs1 imm)
      = (rf.set rd (rf.get rs1 + signExtend12 imm), ws) := rfl

theorem execInstrRF_slli' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (sh : BitVec 6) :
    execInstrRF ro b rf ws (.SLLI rd rs1 sh)
      = (rf.set rd (rf.get rs1 <<< sh.toNat), ws) := rfl

theorem execInstrRF_or' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 rs2 : Reg) :
    execInstrRF ro b rf ws (.OR rd rs1 rs2)
      = (rf.set rd (rf.get rs1 ||| rf.get rs2), ws) := rfl

/-- An `lbu` at the empty writable window reads the read-only region,
    unconditionally. -/
theorem execInstrRF_lbu_nil (ro : Region) (b : Word) (rf : RegFile)
    (rd rs1 : Reg) (ofs : BitVec 12) :
    execInstrRF ro b rf [] (.LBU rd rs1 ofs)
      = (rf.set rd (BitVec.zeroExtend 64
          (ro.byteAt (rf.get rs1 + signExtend12 ofs))), []) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg (by unfold inRw; simp only [List.length_nil]; omega)]

/-- A load VC at the empty writable window is the read-only obligation. -/
theorem edd_vc_nil (b : Word) (ro : Region) (a : Word) (n : Nat)
    (h : ro.loadOk a n) (hn : 0 < n) :
    if inRw b ([] : List (BitVec 8)) a n
    then (Region.mk b ([] : List (BitVec 8))).loadOk a n
    else ro.loadOk a n := by
  rw [if_neg (by unfold inRw; simp only [List.length_nil]; omega)]
  exact h

/-! ## The stage block -/

/-- The BE-u32 assembly block (`.Ledd_zdone`). -/
def eddStage : List Instr :=
  [ .LBU .x6 .x10 (28 : BitVec 12), .SLLI .x6 .x6 (24 : BitVec 6),
    .LBU .x7 .x10 (29 : BitVec 12), .SLLI .x7 .x7 (16 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (30 : BitVec 12), .SLLI .x7 .x7 (8 : BitVec 6),
    .OR .x6 .x6 .x7,
    .LBU .x7 .x10 (31 : BitVec 12), .OR .x6 .x6 .x7 ]

/-! ## The derivation -/

/-- Proof-first `edd_be32_eq`: header-reloaded zero scan over the high
    28 bytes (break → shared `ne` tail), then the BE-u32 compare stage
    into the same tail. -/
def eddDeriv (ptr : Word) (bs : List (BitVec 8)) (K : Word) :
    DCode (Region.mk ptr bs) RwRegion.empty
      (fun rf _ A => eddStatic ptr bs K rf ∧ A = empAssertion)
      (fun rf _ A => rf.get .x10 = eddOut ptr bs K ∧ A = empAssertion) :=
  DCode.seq
    ((DCode.block "init" [.LI .x5 (0 : Word)] (by decide)
      (fun h => absurd h (by decide))
      (by
        rintro rf ws A _ ⟨⟨h10, h11, hbs⟩, hA⟩
        simp only [execBlock_cons, execBlock_nil, execInstrRF_li']
        refine ⟨?_, ⟨?_, ?_, hbs⟩, hA⟩
        · rw [RegFile.get_set_self _ _ _ (by decide)]
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), h10]
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), h11])
      : DCode (Region.mk ptr bs) RwRegion.empty
          (fun rf _ A => eddStatic ptr bs K rf ∧ A = empAssertion)
          (fun rf _ A => rf.get .x5 = (0 : Word) ∧ eddStatic ptr bs K rf
            ∧ A = empAssertion)))
    (DCode.dretWhileHeaderBreak "zscan" (.bne .x5 .x6) 28
      (eddInv ptr bs K) (eddMid ptr bs K) (eddEnd ptr bs K) (.bne .x28 .x0)
      [(eddStage, .bne .x6 .x11)]
      (eddCinv ptr bs K) (eddBad ptr bs K)
      -- header family (reloaded `li t1, 28`)
      (fun x =>
        DCode.block "hdr" [.LI .x6 (28 : Word)] (by decide)
          (fun h => absurd h (by decide))
          (by
            intro rf ws A _ hpre
            simp only [execBlock_cons, execBlock_nil, execInstrRF_li']
            cases x with
            | none =>
                obtain ⟨h5, ⟨h10, h11, hbs⟩, hA⟩ := hpre
                refine ⟨?_, ?_, Nat.zero_le 28, ?_, ⟨?_, ?_, hbs⟩, hA⟩
                · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
                    h5]
                  rfl
                · rw [RegFile.get_set_self _ _ _ (by decide)]
                · intro j hj; omega
                · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
                    h10]
                · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
                    h11]
            | some i =>
                obtain ⟨hi, h5, hin, hz, ⟨h10, h11, hbs⟩, hA⟩ := hpre
                refine ⟨?_, ?_, by omega, hz, ⟨?_, ?_, hbs⟩, hA⟩
                · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
                    h5]
                · rw [RegFile.get_set_self _ _ _ (by decide)]
                · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
                    h10]
                · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
                    h11]))
      -- body prefix: load the next high byte
      (fun i =>
        DCode.block "byte" [.ADD .x7 .x10 .x5, .LBU .x28 .x7 (0 : BitVec 12)]
          (by decide)
          (fun _ rf ws A hlen hpre => by
            obtain ⟨_hi, ⟨h5, _h6, hile, _hz, ⟨h10, _h11, hbs⟩, _hA⟩, hg⟩ :=
              hpre
            have hin : i < 28 := by
              simp only [Cond.holds, ne_eq] at hg
              rcases Nat.lt_or_ge i 28 with h | h
              · exact h
              · exact absurd (by omega : i = 28)
                  (fun he => hg (by rw [h5, _h6, he]; rfl))
            obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hlen
            refine ⟨trivial, ?_, trivial⟩
            exact edd_vc_nil _ _
              ((rf.set .x7 (rf.get .x10 + rf.get .x5)).get .x7
                + signExtend12 (0 : BitVec 12)) 1
              (by
                rw [RegFile.get_set_self _ _ _ (by decide), h10, h5,
                  show signExtend12 (0 : BitVec 12) = (0 : Word) from
                    by decide]
                show 1 ∣ (ptr + BitVec.ofNat 64 i + 0 - ptr).toNat
                  ∧ (ptr + BitVec.ofNat 64 i + 0 - ptr).toNat + 1
                    ≤ bs.length
                rw [show (ptr + BitVec.ofNat 64 i + 0 - ptr).toNat = i from
                  by bv_omega]
                exact ⟨Nat.one_dvd i, by omega⟩)
              (by omega))
          (by
            rintro rf ws A hlen ⟨_hi, ⟨h5, _h6, hile, hz, ⟨h10, h11, hbs⟩, hA⟩,
              hg⟩
            have hin : i < 28 := by
              simp only [Cond.holds, ne_eq] at hg
              rcases Nat.lt_or_ge i 28 with h | h
              · exact h
              · exact absurd (by omega : i = 28)
                  (fun he => hg (by rw [h5, _h6, he]; rfl))
            obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hlen
            simp only [execBlock_cons, execBlock_nil, execInstrRF_add',
              execInstrRF_lbu_nil]
            refine ⟨?_, hin, ?_, hz, ⟨?_, ?_, hbs⟩, hA⟩
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), h5]
            · rw [RegFile.get_set_self _ _ _ (by decide),
                RegFile.get_set_self _ _ _ (by decide), h10, h5,
                show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
              show BitVec.zeroExtend 64
                  ((Region.mk ptr bs).byteAt (ptr + BitVec.ofNat 64 i + 0))
                = eddB ptr bs i
              rw [show ptr + BitVec.ofNat 64 i + 0 = ptr + BitVec.ofNat 64 i
                from by bv_omega]
              rfl
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7), h10]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7), h11]))
      -- body suffix: bump the counter
      (fun i =>
        DCode.block "bump" [.ADDI .x5 .x5 (1 : BitVec 12)] (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ ⟨_hi, ⟨h5, hin, h28, hz, ⟨h10, h11, hbs⟩, hA⟩,
              hnbr⟩
            simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hnbr
            simp only [execBlock_cons, execBlock_nil, execInstrRF_addi']
            refine ⟨?_, hin, ?_, ⟨?_, ?_, hbs⟩, hA⟩
            · rw [RegFile.get_set_self _ _ _ (by decide), h5,
                show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
              bv_omega
            · intro j hj
              rcases Nat.lt_or_ge j i with h | h
              · exact hz j h
              · have : j = i := by omega
                subst this
                rw [← h28]
                exact hnbr
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), h10]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), h11]))
      -- exhaustion: at i = 28 the guard must fail
      (by
        rintro rf ws A ⟨h5, h6, _hile, _hz, _hstat, _hA⟩
        simp only [Cond.holds, ne_eq, not_not]
        rw [h5, h6]
        rfl)
      -- loop exit lands in the cascade's entry invariant
      (by
        rintro rf ws A ⟨⟨i, hile, h5, h6, _hile', hz, hstat, hA⟩, hng⟩
        simp only [Cond.holds, ne_eq, not_not] at hng
        have : i = 28 := by
          rw [h5, h6] at hng
          bv_omega
        subst this
        exact ⟨hz, hstat, hA⟩)
      -- the compare stage's chain obligations
      ⟨⟨rfl,
        (fun _ rf ws A hlen hpre => by
          obtain ⟨_hz, ⟨h10, _h11, hbs⟩, _hA⟩ := hpre
          obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hlen
          refine ⟨?_, trivial, ?_, trivial, trivial, ?_, trivial, trivial,
            ?_, trivial, trivial⟩
          · exact edd_vc_nil _ _
              (rf.get .x10 + signExtend12 (28 : BitVec 12)) 1
              (by
                rw [h10, show signExtend12 (28 : BitVec 12) = (28 : Word)
                  from by decide]
                show 1 ∣ (ptr + 28 - ptr).toNat
                  ∧ (ptr + 28 - ptr).toNat + 1 ≤ bs.length
                rw [show (ptr + (28 : Word) - ptr).toNat = 28 from by
                  bv_omega]
                exact ⟨by omega, by omega⟩)
              (by omega)
          · refine edd_vc_nil _ _ _ 1 ?_ (by omega)
            simp only [execInstrRF_lbu_nil, execInstrRF_slli',
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6)]
            rw [h10, show signExtend12 (29 : BitVec 12)
              = (29 : Word) from by decide]
            show 1 ∣ (ptr + 29 - ptr).toNat
              ∧ (ptr + 29 - ptr).toNat + 1 ≤ bs.length
            rw [show (ptr + (29 : Word) - ptr).toNat = 29 from by
              bv_omega]
            exact ⟨by omega, by omega⟩
          · refine edd_vc_nil _ _ _ 1 ?_ (by omega)
            simp only [execInstrRF_lbu_nil, execInstrRF_slli',
              execInstrRF_or',
              RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
              RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7)]
            rw [h10, show signExtend12 (30 : BitVec 12)
              = (30 : Word) from by decide]
            show 1 ∣ (ptr + 30 - ptr).toNat
              ∧ (ptr + 30 - ptr).toNat + 1 ≤ bs.length
            rw [show (ptr + (30 : Word) - ptr).toNat = 30 from by
              bv_omega]
            exact ⟨by omega, by omega⟩
          · refine edd_vc_nil _ _ _ 1 ?_ (by omega)
            simp only [execInstrRF_lbu_nil, execInstrRF_slli',
              execInstrRF_or',
              RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
              RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7)]
            rw [h10, show signExtend12 (31 : BitVec 12)
              = (31 : Word) from by decide]
            show 1 ∣ (ptr + 31 - ptr).toNat
              ∧ (ptr + 31 - ptr).toNat + 1 ≤ bs.length
            rw [show (ptr + (31 : Word) - ptr).toNat = 31 from by
              bv_omega]
            exact ⟨by omega, by omega⟩),
        (by
          intro rf ws A hstep hnc
          obtain ⟨rf0, ws0, hlen, ⟨hz, ⟨h10, h11, hbs⟩, hA⟩, hrf, _hws⟩ := hstep
          obtain rfl : ws0 = [] := List.eq_nil_of_length_eq_zero hlen
          subst hrf
          simp only [Cond.holds, ne_eq, not_not, eddStage, execBlock_cons,
            execBlock_nil, execInstrRF_lbu_nil, execInstrRF_slli',
            execInstrRF_or'] at hnc
          simp only [RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
            RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7)] at hnc
          rw [h10, h11,
            show signExtend12 (28 : BitVec 12) = BitVec.ofNat 64 28 from
              by decide,
            show signExtend12 (29 : BitVec 12) = BitVec.ofNat 64 29 from
              by decide,
            show signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 from
              by decide,
            show signExtend12 (31 : BitVec 12) = BitVec.ofNat 64 31 from
              by decide,
            show BitVec.toNat (24 : BitVec 6) = 24 from by decide,
            show BitVec.toNat (16 : BitVec 6) = 16 from by decide,
            show BitVec.toNat (8 : BitVec 6) = 8 from by decide] at hnc
          exact ⟨⟨hz, hnc⟩, hA⟩),
        (by
          intro rf ws A hstep hc
          obtain ⟨rf0, ws0, hlen, ⟨hz, ⟨h10, h11, hbs⟩, hA⟩, hrf, _hws⟩ := hstep
          obtain rfl : ws0 = [] := List.eq_nil_of_length_eq_zero hlen
          subst hrf
          simp only [Cond.holds, ne_eq, eddStage, execBlock_cons,
            execBlock_nil, execInstrRF_lbu_nil, execInstrRF_slli',
            execInstrRF_or'] at hc
          simp only [RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
            RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7)] at hc
          rw [h10, h11,
            show signExtend12 (28 : BitVec 12) = BitVec.ofNat 64 28 from
              by decide,
            show signExtend12 (29 : BitVec 12) = BitVec.ofNat 64 29 from
              by decide,
            show signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 from
              by decide,
            show signExtend12 (31 : BitVec 12) = BitVec.ofNat 64 31 from
              by decide,
            show BitVec.toNat (24 : BitVec 6) = 24 from by decide,
            show BitVec.toNat (16 : BitVec 6) = 16 from by decide,
            show BitVec.toNat (8 : BitVec 6) = 8 from by decide] at hc
          exact ⟨fun hok => hc hok.2, hA⟩)⟩,
       trivial⟩
      -- ok tail
      (DCode.seq
        (DCode.block "eq" [.LI .x10 (1 : Word)] (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ ⟨hok, hA⟩
            simp only [execBlock_cons, execBlock_nil, execInstrRF_li']
            refine ⟨?_, hA⟩
            rw [RegFile.get_set_self _ _ _ (by decide), eddOut, if_pos hok]))
        (DCode.retJalr "eqr"))
      -- shared bad tail
      (DCode.seq
        (DCode.block "ne" [.LI .x10 (0 : Word)] (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ (⟨hnok, hA⟩ | ⟨⟨i, hin, _h5, _hin', h28, _hz,
                _hstat, hA⟩, hbr⟩)
            · simp only [execBlock_cons, execBlock_nil, execInstrRF_li']
              refine ⟨?_, hA⟩
              rw [RegFile.get_set_self _ _ _ (by decide), eddOut, if_neg hnok]
            · simp only [Cond.holds, RegFile.get_x0, ne_eq] at hbr
              simp only [execBlock_cons, execBlock_nil, execInstrRF_li']
              refine ⟨?_, hA⟩
              rw [RegFile.get_set_self _ _ _ (by decide), eddOut,
                if_neg (fun hok => hbr (h28.trans (hok.1 i hin)))]))
        (DCode.retJalr "ner")))

/-! ## The generated code and spec -/

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

/-- The generated code (both return tails are IN the code). -/
def eddBe32Eq_prog : Program :=
  (eddDeriv 0 [] 0).stmt.flatten 0

-- Pinned instruction sequence (build-time evaluation): byte-identical to
-- the previously hand-written routine.
#guard (eddBe32Eq_prog : List Instr) ==
    [ .LI .x5 (0 : Word),
      .LI .x6 (28 : Word),
      .BEQ .x5 .x6 (24 : BitVec 13),
      .ADD .x7 .x10 .x5,
      .LBU .x28 .x7 (0 : BitVec 12),
      .BNE .x28 .x0 (64 : BitVec 13),
      .ADDI .x5 .x5 (1 : BitVec 12),
      .JAL .x0 (-24 : BitVec 21),
      .LBU .x6 .x10 (28 : BitVec 12),
      .SLLI .x6 .x6 (24 : BitVec 6),
      .LBU .x7 .x10 (29 : BitVec 12),
      .SLLI .x7 .x7 (16 : BitVec 6),
      .OR .x6 .x6 .x7,
      .LBU .x7 .x10 (30 : BitVec 12),
      .SLLI .x7 .x7 (8 : BitVec 6),
      .OR .x6 .x6 .x7,
      .LBU .x7 .x10 (31 : BitVec 12),
      .OR .x6 .x6 .x7,
      .BNE .x6 .x11 (12 : BitVec 13),
      .LI .x10 (1 : Word),
      .JALR .x0 .x1 (0 : BitVec 12),
      .LI .x10 (0 : Word),
      .JALR .x0 .x1 (0 : BitVec 12) ]

#guard eddBe32Eq_prog.length = 23

-- The code does not depend on the ghost arguments (sampled).
#guard (((eddDeriv 8 [0, 0] 3).stmt.flatten 0) : List Instr)
    == (eddBe32Eq_prog : List Instr)

/-- The generated multi-exit spec: the `ra`-framed triple at any base and
    aligned return address — `a0` ends as the acceptance flag. -/
theorem eddBe32Eq_retSpec (ptr : Word) (bs : List (BitVec 8)) (K : Word)
    (base ret : Word)
    (hwf : (Region.mk ptr bs).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (eddDeriv ptr bs K).stmt.steps base ret
      (CodeReq.ofProg base ((eddDeriv ptr bs K).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk ptr bs) RwRegion.empty
          (fun rf _ A => eddStatic ptr bs K rf ∧ A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk ptr bs) RwRegion.empty
          (fun rf _ A => rf.get .x10 = eddOut ptr bs K
            ∧ A = empAssertion)) :=
  DCode.retSpec (eddDeriv ptr bs K) base ret
    hwf RwRegion.empty_wf halign (fun _ _ h => h)

end EddBe32EqSAsm

end EvmAsm.Codegen
