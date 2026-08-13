/-
  EvmAsm.Codegen.Programs.U256FromU64BeSAsm

  Verified SAsm port of `u256_from_u64_be` (bead evm-asm-4ch8f.13.8): write
  the register-resident u64 in `a0` as a zero-extended 32-byte big-endian u256
  at the destination pointer in `a1`.

  Source (`u256FromU64Be_prog` in U256.lean): three aligned zero dword stores
  for bytes 0..23, followed by eight byte stores for bytes 24..31.

  Spec-only module (no emitted-code change).  Byte identity is pinned by
  `u256FromU64BeBody.flatten 0 ++ [ret] = u256FromU64Be_prog`.
-/

import EvmAsm.Codegen.GuestLayout
import EvmAsm.Codegen.Programs.U256Prog
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256FromU64BeSAsm

/-- The `k`-th big-endian byte of `v`, MSB first. -/
def beByte (v : Word) (k : Nat) : BitVec 8 :=
  BitVec.truncate 8 (v >>> (56 - 8 * k))

/-- The 32-byte big-endian u256 obtained by zero-extending a u64. -/
def u256FromU64Bytes (v : Word) : List (BitVec 8) :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, beByte v 0, beByte v 1, beByte v 2, beByte v 3,
   beByte v 4, beByte v 5, beByte v 6, beByte v 7]

#guard u256FromU64Bytes 0x0102030405060708 =
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem length_u256FromU64Bytes (v : Word) :
    (u256FromU64Bytes v).length = 32 := by
  simp [u256FromU64Bytes]

def u256FromU64BeInstrs : List Instr :=
  [ .SD .x11 .x0 (0 : BitVec 12),
    .SD .x11 .x0 (8 : BitVec 12),
    .SD .x11 .x0 (16 : BitVec 12),
    .SRLI .x5 .x10 (56 : BitVec 6),
    .SB .x11 .x5 (24 : BitVec 12),
    .SRLI .x5 .x10 (48 : BitVec 6),
    .SB .x11 .x5 (25 : BitVec 12),
    .SRLI .x5 .x10 (40 : BitVec 6),
    .SB .x11 .x5 (26 : BitVec 12),
    .SRLI .x5 .x10 (32 : BitVec 6),
    .SB .x11 .x5 (27 : BitVec 12),
    .SRLI .x5 .x10 (24 : BitVec 6),
    .SB .x11 .x5 (28 : BitVec 12),
    .SRLI .x5 .x10 (16 : BitVec 6),
    .SB .x11 .x5 (29 : BitVec 12),
    .SRLI .x5 .x10 (8 : BitVec 6),
    .SB .x11 .x5 (30 : BitVec 12),
    .SB .x11 .x10 (31 : BitVec 12) ]

def u256FromU64BeBody : Stmt :=
  .block "u256FromU64Be" u256FromU64BeInstrs

def writeAllBytes (ws : List (BitVec 8)) (v : Word) : List (BitVec 8) :=
  setBytes
      (setBytes
        (setBytes
          (setBytes
            (setBytes
              (setBytes
                (setBytes
                  (setBytes
                    (setBytes
                      (setBytes
                        (setBytes ws 0 (dwordBytes (0 : Word)))
                        8 (dwordBytes (0 : Word)))
                      16 (dwordBytes (0 : Word)))
                    24 [beByte v 0])
                  25 [beByte v 1])
                26 [beByte v 2])
              27 [beByte v 3])
            28 [beByte v 4])
          29 [beByte v 5])
        30 [beByte v 6])
      31 [beByte v 7]

private theorem writeAllBytes_eq (ws : List (BitVec 8)) (v : Word) (h : ws.length = 32) :
    writeAllBytes ws v = u256FromU64Bytes v := by
  apply List.ext_getElem
  · simp only [writeAllBytes, u256FromU64Bytes, length_setBytes, h, List.length_cons,
      List.length_nil]
  · intro i hleft hright
    simp only [writeAllBytes, length_setBytes, h] at hleft
    interval_cases i <;> simp [writeAllBytes, u256FromU64Bytes, dwordBytes, setBytes] <;> decide

/-- `u256_from_u64_be`'s `Fn`.

    ⚠️ The ambient assertion is PINNED to `empAssertion` in both `pre` and
    `post` (#12244).  This routine has no read-only input region — it
    materializes its 32 output bytes from the register `v` alone — so `emp` is
    the honest ambient, and an ambient-agnostic contract would look more
    general while being strictly less USABLE: every flat-lift adapter in
    `Rv64/SAsm/FnFlat.lean` (`Fn.retSpecFlat`'s `hpostEmp`,
    `Fn.retSpecFlatAmbient`'s `hpostAmb`) requires the post to pin the ambient,
    because that is the only way the information survives out of the
    existentially-quantified `asrtOf`.  Leaving it unpinned is what previously
    made this routine unliftable and therefore unrowable. -/
def u256FromU64BeFn (v dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "u256FromU64Be"
  rw := ⟨dst, 32⟩
  pre := fun rf ws A => rf.get .x10 = v ∧ rf.get .x11 = dst ∧ ws = orig ∧
    orig.length = 32 ∧ A = empAssertion
  post := fun _ ws A => ws = u256FromU64Bytes v ∧ A = empAssertion
  body := u256FromU64BeBody

def u256FromU64Be_verified : Program :=
  u256FromU64BeBody.flatten 0

#guard u256FromU64BeBody.flatten 0 = u256FromU64BeInstrs
#guard (u256FromU64Be_verified : List Instr).length = 18
#guard u256FromU64BeBody.flatten 0 = u256FromU64BeBody.flatten 0x80000000
/-- Layout-independence interlock: the body flattens to `u256FromU64Be_prog_of
    L` for an ARBITRARY layout `L`, so the body cannot reference the layout.
    (`rfl` closes it; a future layout reference would make it fail.) -/
theorem u256FromU64BeBody_flatten (L : GuestLayout) :
    u256FromU64BeBody.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
      = u256FromU64Be_prog_of L := rfl



@[simp] private theorem add_sub_self_toNat_0 (dst : Word) : (dst + (0 : Word) - dst).toNat = 0 := by
  have h : dst + (0 : Word) - dst = (0 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_8 (dst : Word) : (dst + (8 : Word) - dst).toNat = 8 := by
  have h : dst + (8 : Word) - dst = (8 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_16 (dst : Word) : (dst + (16 : Word) - dst).toNat = 16 := by
  have h : dst + (16 : Word) - dst = (16 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_24 (dst : Word) : (dst + (24 : Word) - dst).toNat = 24 := by
  have h : dst + (24 : Word) - dst = (24 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_25 (dst : Word) : (dst + (25 : Word) - dst).toNat = 25 := by
  have h : dst + (25 : Word) - dst = (25 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_26 (dst : Word) : (dst + (26 : Word) - dst).toNat = 26 := by
  have h : dst + (26 : Word) - dst = (26 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_27 (dst : Word) : (dst + (27 : Word) - dst).toNat = 27 := by
  have h : dst + (27 : Word) - dst = (27 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_28 (dst : Word) : (dst + (28 : Word) - dst).toNat = 28 := by
  have h : dst + (28 : Word) - dst = (28 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_29 (dst : Word) : (dst + (29 : Word) - dst).toNat = 29 := by
  have h : dst + (29 : Word) - dst = (29 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_30 (dst : Word) : (dst + (30 : Word) - dst).toNat = 30 := by
  have h : dst + (30 : Word) - dst = (30 : Word) := by bv_omega
  rw [h]
  decide

@[simp] private theorem add_sub_self_toNat_31 (dst : Word) : (dst + (31 : Word) - dst).toNat = 31 := by
  have h : dst + (31 : Word) - dst = (31 : Word) := by bv_omega
  rw [h]
  decide

private theorem u256FromU64Be_engine (rf : RegFile) (ws : List (BitVec 8))
    (v dst : Word) (hx10 : rf.get .x10 = v) (hx11 : rf.get .x11 = dst)
    (_hws : ws.length = 32) :
    (execBlock Region.empty dst rf ws u256FromU64BeInstrs).2 = writeAllBytes ws v := by
  have e0 : (rf.get .x11 + signExtend12 (0 : BitVec 12) - dst).toNat = 0 := by
    rw [hx11, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    exact add_sub_self_toNat_0 dst
  have e8 : (rf.get .x11 + signExtend12 (8 : BitVec 12) - dst).toNat = 8 := by
    rw [hx11, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
    exact add_sub_self_toNat_8 dst
  have e16 : (rf.get .x11 + signExtend12 (16 : BitVec 12) - dst).toNat = 16 := by
    rw [hx11, show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
    exact add_sub_self_toNat_16 dst
  have e24 : (rf.get .x11 + signExtend12 (24 : BitVec 12) - dst).toNat = 24 := by
    rw [hx11, show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]
    exact add_sub_self_toNat_24 dst
  have e25 : (rf.get .x11 + signExtend12 (25 : BitVec 12) - dst).toNat = 25 := by
    rw [hx11, show signExtend12 (25 : BitVec 12) = (25 : Word) from by decide]
    exact add_sub_self_toNat_25 dst
  have e26 : (rf.get .x11 + signExtend12 (26 : BitVec 12) - dst).toNat = 26 := by
    rw [hx11, show signExtend12 (26 : BitVec 12) = (26 : Word) from by decide]
    exact add_sub_self_toNat_26 dst
  have e27 : (rf.get .x11 + signExtend12 (27 : BitVec 12) - dst).toNat = 27 := by
    rw [hx11, show signExtend12 (27 : BitVec 12) = (27 : Word) from by decide]
    exact add_sub_self_toNat_27 dst
  have e28 : (rf.get .x11 + signExtend12 (28 : BitVec 12) - dst).toNat = 28 := by
    rw [hx11, show signExtend12 (28 : BitVec 12) = (28 : Word) from by decide]
    exact add_sub_self_toNat_28 dst
  have e29 : (rf.get .x11 + signExtend12 (29 : BitVec 12) - dst).toNat = 29 := by
    rw [hx11, show signExtend12 (29 : BitVec 12) = (29 : Word) from by decide]
    exact add_sub_self_toNat_29 dst
  have e30 : (rf.get .x11 + signExtend12 (30 : BitVec 12) - dst).toNat = 30 := by
    rw [hx11, show signExtend12 (30 : BitVec 12) = (30 : Word) from by decide]
    exact add_sub_self_toNat_30 dst
  have e31 : (rf.get .x11 + signExtend12 (31 : BitVec 12) - dst).toNat = 31 := by
    rw [hx11, show signExtend12 (31 : BitVec 12) = (31 : Word) from by decide]
    exact add_sub_self_toNat_31 dst
  simp only [u256FromU64BeInstrs, execBlock_cons, execBlock_nil,
    execInstrRF, aluSem, loadSem, storeSem, RegFile.get_x0, RegFile.get_set_self,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, e0, e8, e16, e24,
    e25, e26, e27, e28, e29, e30, e31, hx10]
  rw [show (56 : BitVec 6).toNat = 56 from by decide,
    show (48 : BitVec 6).toNat = 48 from by decide,
    show (40 : BitVec 6).toNat = 40 from by decide,
    show (32 : BitVec 6).toNat = 32 from by decide,
    show (24 : BitVec 6).toNat = 24 from by decide,
    show (16 : BitVec 6).toNat = 16 from by decide,
    show (8 : BitVec 6).toNat = 8 from by decide]
  rfl

private theorem u256FromU64Be_blockVCs (rf : RegFile) (ws : List (BitVec 8))
    (v dst : Word) (hx10 : rf.get .x10 = v) (hx11 : rf.get .x11 = dst)
    (hws : ws.length = 32) :
    blockVCs Region.empty dst rf ws u256FromU64BeInstrs := by
  have e0 : (rf.get .x11 + signExtend12 (0 : BitVec 12) - dst).toNat = 0 := by
    rw [hx11, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    exact add_sub_self_toNat_0 dst
  have e8 : (rf.get .x11 + signExtend12 (8 : BitVec 12) - dst).toNat = 8 := by
    rw [hx11, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
    exact add_sub_self_toNat_8 dst
  have e16 : (rf.get .x11 + signExtend12 (16 : BitVec 12) - dst).toNat = 16 := by
    rw [hx11, show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
    exact add_sub_self_toNat_16 dst
  have e24 : (rf.get .x11 + signExtend12 (24 : BitVec 12) - dst).toNat = 24 := by
    rw [hx11, show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]
    exact add_sub_self_toNat_24 dst
  have e25 : (rf.get .x11 + signExtend12 (25 : BitVec 12) - dst).toNat = 25 := by
    rw [hx11, show signExtend12 (25 : BitVec 12) = (25 : Word) from by decide]
    exact add_sub_self_toNat_25 dst
  have e26 : (rf.get .x11 + signExtend12 (26 : BitVec 12) - dst).toNat = 26 := by
    rw [hx11, show signExtend12 (26 : BitVec 12) = (26 : Word) from by decide]
    exact add_sub_self_toNat_26 dst
  have e27 : (rf.get .x11 + signExtend12 (27 : BitVec 12) - dst).toNat = 27 := by
    rw [hx11, show signExtend12 (27 : BitVec 12) = (27 : Word) from by decide]
    exact add_sub_self_toNat_27 dst
  have e28 : (rf.get .x11 + signExtend12 (28 : BitVec 12) - dst).toNat = 28 := by
    rw [hx11, show signExtend12 (28 : BitVec 12) = (28 : Word) from by decide]
    exact add_sub_self_toNat_28 dst
  have e29 : (rf.get .x11 + signExtend12 (29 : BitVec 12) - dst).toNat = 29 := by
    rw [hx11, show signExtend12 (29 : BitVec 12) = (29 : Word) from by decide]
    exact add_sub_self_toNat_29 dst
  have e30 : (rf.get .x11 + signExtend12 (30 : BitVec 12) - dst).toNat = 30 := by
    rw [hx11, show signExtend12 (30 : BitVec 12) = (30 : Word) from by decide]
    exact add_sub_self_toNat_30 dst
  have e31 : (rf.get .x11 + signExtend12 (31 : BitVec 12) - dst).toNat = 31 := by
    rw [hx11, show signExtend12 (31 : BitVec 12) = (31 : Word) from by decide]
    exact add_sub_self_toNat_31 dst
  simp only [u256FromU64BeInstrs, blockVCs, inRw, execInstrRF, aluSem, loadSem,
    storeSem, RegFile.get_x0, RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
    reduceCtorEq, not_false_eq_true, length_setBytes, hws, hx10, hx11,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show signExtend12 (25 : BitVec 12) = (25 : Word) from by decide,
    show signExtend12 (26 : BitVec 12) = (26 : Word) from by decide,
    show signExtend12 (27 : BitVec 12) = (27 : Word) from by decide,
    show signExtend12 (28 : BitVec 12) = (28 : Word) from by decide,
    show signExtend12 (29 : BitVec 12) = (29 : Word) from by decide,
    show signExtend12 (30 : BitVec 12) = (30 : Word) from by decide,
    show signExtend12 (31 : BitVec 12) = (31 : Word) from by decide]
  repeat constructor <;> simp_all [signExtend12]

theorem u256FromU64BeFn_spec (v dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 32⟩) (base : Word) :
    (u256FromU64BeFn v dst orig).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case u256FromU64Be.u256FromU64Be.mem =>
    rintro rf ws A hlen ⟨hx10, hx11, -, -⟩
    exact u256FromU64Be_blockVCs rf ws v dst hx10 hx11 hlen
  case u256FromU64Be.post =>
    rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨hx10, hx11, hwseq, hlenorig, hAemp⟩, hrfeq, hwseq2⟩
    subst ws₀
    rw [hwseq2]
    simp only [u256FromU64BeFn]
    -- The ambient conjunct (#12244) comes straight from the precondition: the
    -- reach relation threads `A` unchanged through the body.
    refine ⟨?_, hAemp⟩
    rw [u256FromU64Be_engine rf₀ orig v dst hx10 hx11 hlenorig]
    exact writeAllBytes_eq orig v hlenorig

end U256FromU64BeSAsm

end EvmAsm.Codegen
