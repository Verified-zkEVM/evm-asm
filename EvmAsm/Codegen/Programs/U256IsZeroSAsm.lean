/-
  EvmAsm.Codegen.Programs.U256IsZeroSAsm

  Verified SAsm port of `u256_is_zero` (bead evm-asm-4ch8f.13.5): read a
  32-byte buffer at the pointer in `a0`, OR the four little-endian dwords
  together, and return `a0 = 1` iff the OR is zero (i.e. all 32 bytes are
  zero).

  Source asm (leaf, from U256.lean):

      u256_is_zero:
        ld x5, 0(x10)
        ld x6, 8(x10)
        ld x7, 16(x10)
        ld x28, 24(x10)
        or x5, x5, x6
        or x5, x5, x7
        or x5, x5, x28
        sltiu x10, x5, 1
        jalr x0, x1, 0

  Leaf (ret via ra=x1).  Read-only region: the 32-byte input buffer.
  No memory writes; result in register `x10`.

  Spec-only module (no emitted-code change) — no EEST A/B required.
-/

import EvmAsm.Codegen.Programs.U256
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256IsZeroSAsm

/-- The 8 body instructions as a list: 4 dword loads + 3 ORs + 1 SLTIU. -/
def u256IsZeroInstrs : List Instr :=
  [ .LD .x5 .x10 (0 : BitVec 12),
    .LD .x6 .x10 (8 : BitVec 12),
    .LD .x7 .x10 (16 : BitVec 12),
    .LD .x28 .x10 (24 : BitVec 12),
    .OR .x5 .x5 .x6,
    .OR .x5 .x5 .x7,
    .OR .x5 .x5 .x28,
    .SLTIU .x10 .x5 (1 : BitVec 12) ]

/-- The straight-line body. -/
def u256IsZeroBody : Stmt := .block "z" u256IsZeroInstrs

/-- Verified port of `u256_is_zero`: read-only 32-byte buffer, result in `x10`. -/
def u256IsZeroFn (ptr : Word) (bs : List (BitVec 8)) : Fn where
  name := "u256IsZero"
  region := ⟨ptr, bs⟩
  pre := fun rf _ _ => rf.get .x10 = ptr ∧ bs.length = 32
  post := fun rf _ _ => rf.get .x10 = if bs = List.replicate 32 (0 : BitVec 8) then (1 : Word) else 0
  body := u256IsZeroBody

/-- The emitted drop-in replacement (position-independent: no branches). -/
def u256IsZero_verified : Program :=
  u256IsZeroBody.flatten 0

#guard (u256IsZero_verified : List Instr).length = 8
#guard u256IsZeroBody.flatten 0 = u256IsZeroBody.flatten 0x80000000

-- Byte-identity to the emitted routine: the 8 body instructions plus the
-- calling-convention `ret` epilogue reproduce `u256IsZero_prog` exactly.
#guard u256IsZeroBody.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
  = u256IsZero_prog

private theorem se12_0 : signExtend12 (0#12 : BitVec 12) = (0 : Word) := by decide
private theorem se12_8 : signExtend12 (8#12 : BitVec 12) = (8 : Word) := by decide
private theorem se12_16 : signExtend12 (16#12 : BitVec 12) = (16 : Word) := by decide
private theorem se12_24 : signExtend12 (24#12 : BitVec 12) = (24 : Word) := by decide
private theorem se12_1 : signExtend12 (1#12 : BitVec 12) = (1 : Word) := by decide

/-! ## Byte-level helper lemmas -/

/-- `packBytes l = 0` iff all bytes at indices `< 8` are zero, assuming `l`
    has at least 8 elements. -/
private lemma packBytes_eq_zero_iff (l : List (BitVec 8)) (hlen : 8 ≤ l.length) :
    packBytes l = 0 ↔ ∀ k, k < 8 → getByteAt l k = 0 := by
  constructor
  · intro h k hk
    have hk_len : k < l.length := lt_of_lt_of_le hk hlen
    rw [getByteAt, dif_pos hk_len, ← extractByte_packBytes l k hk hk_len, h]
    simp [extractByte]
  · intro h
    unfold packBytes packDword
    -- `packDword` is a big OR of 8 shifted zero-extended bytes.
    -- When each `getByteAt l k = 0` for `k < 8`, every term is 0.
    have h0 : getByteAt l 0 = 0 := h 0 (by decide)
    have h1 : getByteAt l 1 = 0 := h 1 (by decide)
    have h2 : getByteAt l 2 = 0 := h 2 (by decide)
    have h3 : getByteAt l 3 = 0 := h 3 (by decide)
    have h4 : getByteAt l 4 = 0 := h 4 (by decide)
    have h5 : getByteAt l 5 = 0 := h 5 (by decide)
    have h6 : getByteAt l 6 = 0 := h 6 (by decide)
    have h7 : getByteAt l 7 = 0 := h 7 (by decide)
    simp [h0, h1, h2, h3, h4, h5, h6, h7]

/-- If every byte in a list is zero, the list is `replicate (l.length) 0`. -/
private lemma all_zero_eq_replicate (l : List (BitVec 8)) :
    (∀ i (h₁ : i < l.length) (h₂ : i < (List.replicate l.length (0 : BitVec 8)).length),
     l[i]'h₁ = (List.replicate l.length (0 : BitVec 8))[i]'h₂) →
    l = List.replicate l.length (0 : BitVec 8) := by
  intro h
  apply List.ext_getElem
  · simp
  · exact h

/-- A slice `l[k..k+7]` being all zeros (for `l` of length ≥ `k+8`) means
    `l[k+j] = 0` for `j < 8`.  Used to relate `packBytes (l.drop k).take 8 = 0`
    to the underlying bytes of `l`. -/
private lemma drop_take_eq_zero_iff (l : List (BitVec 8)) (k : Nat) (hk : k + 8 ≤ l.length) :
    packBytes ((l.drop k).take 8) = 0 ↔ ∀ j, j < 8 → getByteAt l (k + j) = 0 := by
  have h_len : 8 ≤ ((l.drop k).take 8).length := by
    rw [List.length_take, List.length_drop]
    omega
  have h := packBytes_eq_zero_iff ((l.drop k).take 8) h_len
  rw [h]
  constructor
  · intro h' j hj
    have hkj : k + j < l.length := by omega
    have htake_len : j < ((l.drop k).take 8).length := by
      rw [List.length_take, List.length_drop]
      omega
    have h_drop_len : j < (l.drop k).length := by
      rw [List.length_drop]
      omega
    have h_take := h' j hj
    rw [getByteAt, dif_pos htake_len] at h_take
    -- h_take : ((l.drop k).take 8)[j]'htake_len = 0
    -- Goal: getByteAt l (k + j) = 0
    rw [getByteAt, dif_pos hkj]
    -- Goal: l[k+j]'hkj = 0
    rw [← List.getElem_drop (h := h_drop_len), ← List.getElem_take (h := htake_len)]
    exact h_take
  · intro h' j hj
    have hkj : k + j < l.length := by omega
    have htake_len : j < ((l.drop k).take 8).length := by
      rw [List.length_take, List.length_drop]
      omega
    have h_drop_len : j < (l.drop k).length := by
      rw [List.length_drop]
      omega
    have h_l := h' j hj
    rw [getByteAt, dif_pos hkj] at h_l
    -- h_l : l[k+j]'hkj = 0
    -- Goal: getByteAt ((l.drop k).take 8) j = 0
    rw [getByteAt, dif_pos htake_len]
    -- Goal: ((l.drop k).take 8)[j]'htake_len = 0
    rw [List.getElem_take (h := htake_len), List.getElem_drop (h := h_drop_len)]
    exact h_l

/-- The four dwords OR to zero iff all 32 bytes of the buffer are zero. -/
private lemma dword_or_eq_zero_iff (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (Region.dwordAt ⟨0, bs⟩ (0 : Word) |||
     Region.dwordAt ⟨0, bs⟩ (8 : Word) |||
     Region.dwordAt ⟨0, bs⟩ (16 : Word) |||
     Region.dwordAt ⟨0, bs⟩ (24 : Word) = 0)
    ↔ bs = List.replicate 32 (0 : BitVec 8) := by
  have hd0 : Region.dwordAt ⟨0, bs⟩ (0 : Word) = packBytes ((bs.drop 0).take 8) := by
    unfold Region.dwordAt; simp
  have hd8 : Region.dwordAt ⟨0, bs⟩ (8 : Word) = packBytes ((bs.drop 8).take 8) := by
    unfold Region.dwordAt; simp
  have hd16 : Region.dwordAt ⟨0, bs⟩ (16 : Word) = packBytes ((bs.drop 16).take 8) := by
    unfold Region.dwordAt; simp
  have hd24 : Region.dwordAt ⟨0, bs⟩ (24 : Word) = packBytes ((bs.drop 24).take 8) := by
    unfold Region.dwordAt; simp
  rw [hd0, hd8, hd16, hd24]
  have hlen0 : 0 + 8 ≤ bs.length := by rw [hlen]; omega
  have hlen8 : 8 + 8 ≤ bs.length := by rw [hlen]; omega
  have hlen16 : 16 + 8 ≤ bs.length := by rw [hlen]; omega
  have hlen24 : 24 + 8 ≤ bs.length := by rw [hlen]
  have h_or4 : (packBytes ((bs.drop 0).take 8) ||| packBytes ((bs.drop 8).take 8) |||
                packBytes ((bs.drop 16).take 8) ||| packBytes ((bs.drop 24).take 8) = 0)
    ↔ packBytes ((bs.drop 0).take 8) = 0 ∧ packBytes ((bs.drop 8).take 8) = 0 ∧
      packBytes ((bs.drop 16).take 8) = 0 ∧ packBytes ((bs.drop 24).take 8) = 0 := by
    simp [BitVec.or_eq_zero_iff, and_assoc]
  rw [h_or4]
  rw [drop_take_eq_zero_iff bs 0 hlen0,
    drop_take_eq_zero_iff bs 8 hlen8,
    drop_take_eq_zero_iff bs 16 hlen16,
    drop_take_eq_zero_iff bs 24 hlen24]
  constructor
  · rintro ⟨h0, h8, h16, h24⟩
    have h_all_zero : ∀ i (h : i < bs.length), getByteAt bs i = 0 := by
      intro i hi
      have hi32 : i < 32 := by simpa [hlen] using hi
      by_cases hi0 : i < 8
      · simpa using h0 i hi0
      · by_cases hi8 : i < 16
        · have : i = 8 + (i - 8) := by omega
          rw [this]
          exact h8 (i - 8) (by omega)
        · by_cases hi16 : i < 24
          · have : i = 16 + (i - 16) := by omega
            rw [this]
            exact h16 (i - 16) (by omega)
          · have : i = 24 + (i - 24) := by omega
            rw [this]
            exact h24 (i - 24) (by omega)
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi₁ hi₂
      have h_byte := h_all_zero i hi₁
      rw [getByteAt, dif_pos hi₁] at h_byte
      rw [List.getElem_replicate (by simpa [hlen] using hi₂)]
      exact h_byte
  · intro h
    subst h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [getByteAt, dif_pos (by omega)]
      rw [List.getElem_replicate (by omega)]
    · intro j hj
      rw [getByteAt, dif_pos (by omega)]
      rw [List.getElem_replicate (by omega)]
    · intro j hj
      rw [getByteAt, dif_pos (by omega)]
      rw [List.getElem_replicate (by omega)]
    · intro j hj
      rw [getByteAt, dif_pos (by omega)]
      rw [List.getElem_replicate (by omega)]

/-! ## Engine lemma -/

/-- Engine lemma: stepping the four dword loads, three ORs, and SLTIU through
    the symbolic engine leaves the register file and workspace in known states. -/
private theorem u256IsZero_engine (reg : Region) (rwb : Word) (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = reg.base) (hws : ws.length = 0) :
    (execBlock reg rwb rf ws u256IsZeroInstrs).1.get .x10 =
      (if BitVec.ult (packBytes ((reg.bytes.drop 0).take 8) |||
        packBytes ((reg.bytes.drop 8).take 8) |||
        packBytes ((reg.bytes.drop 16).take 8) |||
        packBytes ((reg.bytes.drop 24).take 8)) (signExtend12 (1 : BitVec 12))
      then (1 : Word) else 0) ∧
    (execBlock reg rwb rf ws u256IsZeroInstrs).2 = [] := by
  obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
  have h_se0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have h_se8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have h_se16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  have h_se24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
  have h_se1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  simp only [u256IsZeroInstrs, execBlock_cons, execBlock_nil, execInstrRF_nil,
    aluSem, loadSem, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
    reduceCtorEq, not_false_eq_true]
  rw [h_se0, h_se8, h_se16, h_se24, h_se1]
  -- Rewrite rf.get .x10 to reg.base so the hd rewrites match
  rw [hx10]
  -- Now the target has: reg.dwordAt (reg.base + 0) etc. on LHS
  -- and packBytes ((reg.bytes.drop 0).take 8) etc. on RHS
  -- Unfold Region.dwordAt on the LHS; need bv_omega for the subtraction
  have hd0 : Region.dwordAt reg (reg.base + (0 : Word)) = packBytes ((reg.bytes.drop 0).take 8) := by
    unfold Region.dwordAt
    have h : (reg.base + (0 : Word) - reg.base).toNat = 0 := by bv_omega
    rw [h]
  have hd8 : Region.dwordAt reg (reg.base + (8 : Word)) = packBytes ((reg.bytes.drop 8).take 8) := by
    unfold Region.dwordAt
    have h : (reg.base + (8 : Word) - reg.base).toNat = 8 := by bv_omega
    rw [h]
  have hd16 : Region.dwordAt reg (reg.base + (16 : Word)) = packBytes ((reg.bytes.drop 16).take 8) := by
    unfold Region.dwordAt
    have h : (reg.base + (16 : Word) - reg.base).toNat = 16 := by bv_omega
    rw [h]
  have hd24 : Region.dwordAt reg (reg.base + (24 : Word)) = packBytes ((reg.bytes.drop 24).take 8) := by
    unfold Region.dwordAt
    have h : (reg.base + (24 : Word) - reg.base).toNat = 24 := by bv_omega
    rw [h]
  rw [hd0, hd8, hd16, hd24]
  refine ⟨rfl, trivial⟩

/-! ## Block address side conditions -/

/-- Address side conditions of the body: each `LD` reads from the
    read-only region at an aligned offset, and the region is 32 bytes so
    all four dword accesses fit. -/
private theorem u256IsZero_blockVCs (reg : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (hx10 : rf.get .x10 = reg.base) (hws : ws.length = 0)
    (hlen : reg.bytes.length = 32) :
    blockVCs reg rwb rf ws u256IsZeroInstrs := by
  obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
  have hx10' : rf.get .x10 = reg.base := hx10
  -- Directly construct the 4 LD side conditions
  have h_ld0 : reg.loadOk (reg.base + signExtend12 (0 : BitVec 12)) 8 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, Region.loadOk]
    have h : (reg.base + (0 : Word) - reg.base).toNat = 0 := by bv_omega
    rw [h, hlen]; simp
  have h_ld8 : reg.loadOk (reg.base + signExtend12 (8 : BitVec 12)) 8 := by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide, Region.loadOk]
    have h : (reg.base + (8 : Word) - reg.base).toNat = 8 := by bv_omega
    rw [h, hlen]; simp
  have h_ld16 : reg.loadOk (reg.base + signExtend12 (16 : BitVec 12)) 8 := by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide, Region.loadOk]
    have h : (reg.base + (16 : Word) - reg.base).toNat = 16 := by bv_omega
    rw [h, hlen]; simp
  have h_ld24 : reg.loadOk (reg.base + signExtend12 (24 : BitVec 12)) 8 := by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide, Region.loadOk]
    have h : (reg.base + (24 : Word) - reg.base).toNat = 24 := by bv_omega
    rw [h, hlen]; simp
  -- Now assemble the blockVCs proof
  simpa [u256IsZeroInstrs, blockVCs, loadSem, storeSem, aluSem, inRw,
    execInstrRF_nil, RegFile.get_set_ne,
    ne_eq, reduceCtorEq, not_false_eq_true, List.length_nil,
    hx10'] using And.intro h_ld0 (And.intro h_ld8 (And.intro h_ld16 h_ld24))

/-! ## Spec theorem -/

theorem u256IsZeroFn_spec (ptr : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk ptr bs).wf) (base : Word) :
    (u256IsZeroFn ptr bs).Spec base := by
  vcgen
  case region => exact ⟨hwf, RwRegion.empty_wf⟩
  case u256IsZero.z.mem =>
    rintro rf ws A hws hpre
    obtain ⟨hx10, hlen⟩ := hpre
    exact u256IsZero_blockVCs (Region.mk ptr bs) 0 rf ws hx10 hws hlen
  case u256IsZero.post =>
    rintro rf ws A hsp
    obtain ⟨rf₀, ws₀, hws₀, hpre₀, hrfeq, hwseq2⟩ := hsp
    obtain ⟨hx10, hlenorig⟩ := hpre₀
    have hws₀_empty : ws₀ = [] := by
      have : (u256IsZeroFn ptr bs).rw.len = 0 := rfl
      rw [this] at hws₀
      exact List.eq_nil_of_length_eq_zero hws₀
    subst hws₀_empty
    rw [hwseq2]
    obtain ⟨h_engine, h_ws⟩ := u256IsZero_engine (Region.mk ptr bs) 0 rf₀ [] hx10 (by simp)
    -- Expand the Fn projections without dsimp (which expands List.replicate)
    have h_post : (u256IsZeroFn ptr bs).post = fun rf _ _ => rf.get .x10 = if bs = List.replicate 32 (0 : BitVec 8) then (1 : Word) else 0 := rfl
    have h_region : (u256IsZeroFn ptr bs).region = ⟨ptr, bs⟩ := rfl
    have h_rw : (u256IsZeroFn ptr bs).rw = RwRegion.empty := rfl
    rw [h_post, h_region, h_rw]
    -- Goal: rf.get Reg.x10 = (if bs = List.replicate 32 (0 : BitVec 8) then (1 : Word) else 0)
    -- Simplify hrfeq to match
    rw [h_region, h_rw] at hrfeq
    -- hrfeq: rf = (execBlock ⟨ptr, bs⟩ RwRegion.empty.base rf₀ [] u256IsZeroInstrs).1
    -- Beta-reduce the goal to apply the post function, without expanding List.replicate
    beta_reduce
    -- Goal: (execBlock ⟨ptr, bs⟩ RwRegion.empty.base rf₀ [] u256IsZeroInstrs).1.get Reg.x10 = if bs = List.replicate 32 (0 : BitVec 8) then (1 : Word) else 0
    -- h_engine: (execBlock { base := ptr, bytes := bs } 0 rf₀ [] u256IsZeroInstrs).1.get Reg.x10 = if (packBytes ...).ult ... = true then 1 else 0
    -- Since RwRegion.empty.base = 0 definitionally and ⟨ptr, bs⟩ = { base := ptr, bytes := bs } definitionally,
    -- h_engine directly matches the goal's LHS.  Prove the RHS equality.
    have h_goal_eq : (if BitVec.ult (packBytes ((bs.drop 0).take 8) |||
      packBytes ((bs.drop 8).take 8) |||
      packBytes ((bs.drop 16).take 8) |||
      packBytes ((bs.drop 24).take 8)) (signExtend12 (1 : BitVec 12)) = true then (1 : Word) else 0)
      = (if bs = List.replicate 32 (0 : BitVec 8) then (1 : Word) else 0) := by
      by_cases h_bs_eq : bs = List.replicate 32 (0 : BitVec 8)
      · rw [if_pos h_bs_eq]
        -- Goal: (if (packBytes ...).ult ... = true then 1 else 0) = 1
        -- Need to show the condition is true
        have hd0 : Region.dwordAt ⟨0, bs⟩ (0 : Word) = packBytes ((bs.drop 0).take 8) := by
          unfold Region.dwordAt; simp
        have hd8 : Region.dwordAt ⟨0, bs⟩ (8 : Word) = packBytes ((bs.drop 8).take 8) := by
          unfold Region.dwordAt; simp
        have hd16 : Region.dwordAt ⟨0, bs⟩ (16 : Word) = packBytes ((bs.drop 16).take 8) := by
          unfold Region.dwordAt; simp
        have hd24 : Region.dwordAt ⟨0, bs⟩ (24 : Word) = packBytes ((bs.drop 24).take 8) := by
          unfold Region.dwordAt; simp
        have h_pb_or_zero : (packBytes ((bs.drop 0).take 8) |||
          packBytes ((bs.drop 8).take 8) |||
          packBytes ((bs.drop 16).take 8) |||
          packBytes ((bs.drop 24).take 8) = 0) ↔ bs = List.replicate 32 (0 : BitVec 8) := by
          rw [← hd0, ← hd8, ← hd16, ← hd24]
          exact dword_or_eq_zero_iff bs hlenorig
        have h_pb_zero : (packBytes ((bs.drop 0).take 8) |||
          packBytes ((bs.drop 8).take 8) |||
          packBytes ((bs.drop 16).take 8) |||
          packBytes ((bs.drop 24).take 8)) = 0 := h_pb_or_zero.mpr h_bs_eq
        have h_se1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
        have h_ult_true : BitVec.ult (packBytes ((bs.drop 0).take 8) |||
          packBytes ((bs.drop 8).take 8) |||
          packBytes ((bs.drop 16).take 8) |||
          packBytes ((bs.drop 24).take 8)) (signExtend12 (1 : BitVec 12)) = true := by
          rw [h_se1, h_pb_zero]
          simp
        rw [if_pos h_ult_true]
      · rw [if_neg h_bs_eq]
        -- Goal: (if (packBytes ...).ult ... = true then 1 else 0) = 0
        -- Need to show the condition is false
        have hd0 : Region.dwordAt ⟨0, bs⟩ (0 : Word) = packBytes ((bs.drop 0).take 8) := by
          unfold Region.dwordAt; simp
        have hd8 : Region.dwordAt ⟨0, bs⟩ (8 : Word) = packBytes ((bs.drop 8).take 8) := by
          unfold Region.dwordAt; simp
        have hd16 : Region.dwordAt ⟨0, bs⟩ (16 : Word) = packBytes ((bs.drop 16).take 8) := by
          unfold Region.dwordAt; simp
        have hd24 : Region.dwordAt ⟨0, bs⟩ (24 : Word) = packBytes ((bs.drop 24).take 8) := by
          unfold Region.dwordAt; simp
        have h_pb_or_zero : (packBytes ((bs.drop 0).take 8) |||
          packBytes ((bs.drop 8).take 8) |||
          packBytes ((bs.drop 16).take 8) |||
          packBytes ((bs.drop 24).take 8) = 0) ↔ bs = List.replicate 32 (0 : BitVec 8) := by
          rw [← hd0, ← hd8, ← hd16, ← hd24]
          exact dword_or_eq_zero_iff bs hlenorig
        have h_pb_ne_zero : (packBytes ((bs.drop 0).take 8) |||
          packBytes ((bs.drop 8).take 8) |||
          packBytes ((bs.drop 16).take 8) |||
          packBytes ((bs.drop 24).take 8)) ≠ 0 := by
          intro h; apply h_bs_eq; exact h_pb_or_zero.mp h
        have h_ult_false : ¬ BitVec.ult (packBytes ((bs.drop 0).take 8) |||
          packBytes ((bs.drop 8).take 8) |||
          packBytes ((bs.drop 16).take 8) |||
          packBytes ((bs.drop 24).take 8)) (signExtend12 (1 : BitVec 12)) = true := by
          rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
          rw [BitVec.ult_iff_toNat_lt]
          have h1 : (1 : Word).toNat = 1 := by decide
          rw [h1]
          intro hlt
          apply h_pb_ne_zero
          have hzero : (packBytes ((bs.drop 0).take 8) |||
            packBytes ((bs.drop 8).take 8) |||
            packBytes ((bs.drop 16).take 8) |||
            packBytes ((bs.drop 24).take 8)).toNat = 0 := by omega
          exact BitVec.toNat_inj.mp hzero
        rw [if_neg h_ult_false]
    -- Rewrite the goal's LHS using hrfeq to match h_engine's LHS
    rw [hrfeq]
    -- Goal: (execBlock ... RwRegion.empty.base ...).1.get Reg.x10 = if bs = List.replicate 32 0 then 1 else 0
    -- h_engine's LHS: (execBlock ... 0 ...).1.get Reg.x10  (0 = RwRegion.empty.base definitionally)
    -- h_goal_eq: (if BitVec.ult ... = true then 1 else 0) = (if bs = List.replicate 32 0 then 1 else 0)
    exact h_engine.trans h_goal_eq

end U256IsZeroSAsm

end EvmAsm.Codegen
