/-
  EvmAsm.Codegen.Programs.U256MinSAsm

  `u256_min` (and `u256_max`) via the **dynamic selected-read / copy-tail
  combinator** (`EvmAsm/Rv64/SAsm/SelectedRead.lean`, bead evm-asm-otbab) —
  the acceptance consumers.

  The routine byte-walks the two 32-byte big-endian operands, breaks to a
  selector on the first differing byte (`x5 := aPtr` if `a` is smaller or
  the operands are equal, `x5 := bPtr` otherwise), and the SHARED tail
  copies 4 dwords through the dynamically-chosen `x5` into `out`:

  ```
        li   t0, 0 ; li x31, 32
  hdr:  beq  t0, x31, .pick_a          -- all 32 bytes equal
        add  t1, a0, t0 ; add t2, a1, t0
        lbu  x28, 0(t1) ; lbu x29, 0(t2)
        bltu x28, x29, .pick_a         -- a[i] < b[i]
        bltu x29, x28, .pick_b         -- b[i] < a[i]
        addi t0, t0, 1 ; j hdr
  .pick_a: mv x5, a0 ; j .copy
  .pick_b: mv x5, a1
  .copy: 4 × (ld t1, 8k(x5) ; sd t1, 8k(a2))
        li a0, 0 ; ret
  ```

  The post-join region choice is the pointer pinned to
  `if beBytesToNat as ≤ beBytesToNat bs then aPtr else bPtr`; the shared
  copy tail is ONE `selectedDwordCopy_spec` instance per selector case
  (other operand framed).  **Genuine post**: the output bytes are
  byte-for-byte the numerically-smaller operand (`a` on ties — big-endian
  lexicographic order IS numeric order, proven by
  `beBytesToNat_lt_of_prefix_lt`), both inputs untouched.

  Byte-transparent: the spec is stated at the `#guard`-tied
  `GuestAddrs.u256_min` over the emitted `u256Min_prog` directly (and the
  copy tail's generator is `rfl`-tied to the emitted sub-list); `u256_max`
  is the same shape with the selector inverted.
-/

import EvmAsm.Codegen.Programs.U256
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.SAsm.RetForwardJoin
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Crypto.PowLadder

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace U256MinSAsm

-- Address anchor.
#guard GuestAddrs.u256_min = 0x80024da4

-- The shared copy tail of the emitted program IS the combinator's
-- generator (kernel-checked byte tie).
theorem u256Min_copyTail_tie :
    dwordCopyProgFrom .x5 .x12 .x6 0 4
      = [ .LD .x6 .x5 (0 : BitVec 12), .SD .x12 .x6 (0 : BitVec 12),
          .LD .x6 .x5 (8 : BitVec 12), .SD .x12 .x6 (8 : BitVec 12),
          .LD .x6 .x5 (16 : BitVec 12), .SD .x12 .x6 (16 : BitVec 12),
          .LD .x6 .x5 (24 : BitVec 12), .SD .x12 .x6 (24 : BitVec 12) ] := rfl

-- ============================================================================
-- §1  Big-endian lexicographic order IS numeric order
-- ============================================================================

private theorem beBytesToNat_foldl (bs : List (BitVec 8)) (acc : Nat) :
    bs.foldl (fun a b => a * 256 + b.toNat) acc
      = acc * 256 ^ bs.length + beBytesToNat bs := by
  induction bs generalizing acc with
  | nil => simp [beBytesToNat]
  | cons b rest ih =>
      show rest.foldl _ (acc * 256 + b.toNat) = _
      rw [ih (acc * 256 + b.toNat)]
      have hb : beBytesToNat (b :: rest)
          = b.toNat * 256 ^ rest.length + beBytesToNat rest := by
        show rest.foldl _ (0 * 256 + b.toNat) = _
        rw [ih (0 * 256 + b.toNat), Nat.zero_mul, Nat.zero_add]
      rw [hb, List.length_cons, Nat.pow_succ]
      rw [Nat.add_mul, Nat.mul_comm (256 ^ rest.length) 256, ← Nat.mul_assoc]
      omega

private theorem beBytesToNat_append (xs ys : List (BitVec 8)) :
    beBytesToNat (xs ++ ys)
      = beBytesToNat xs * 256 ^ ys.length + beBytesToNat ys := by
  unfold beBytesToNat
  rw [List.foldl_append]
  exact beBytesToNat_foldl ys _

private theorem beBytesToNat_bound (bs : List (BitVec 8)) :
    beBytesToNat bs < 256 ^ bs.length := by
  have h := beBytesToNat_lt bs
  have : (256 : Nat) ^ bs.length = 2 ^ (8 * bs.length) := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]
  omega

/-- **BE lexicographic < implies numeric <**: equal prefixes and a smaller
    byte at the first difference give a smaller value.  (Public: also
    consumed by `U256LtBeSAsm`.) -/
theorem beBytesToNat_lt_of_prefix_lt (as bs : List (BitVec 8))
    (hlen : as.length = bs.length) (i : Nat) (hia : i < as.length)
    (hpref : ∀ j, j < i → as.getD j 0 = bs.getD j 0)
    (hlt : (as.getD i 0).toNat < (bs.getD i 0).toNat) :
    beBytesToNat as < beBytesToNat bs := by
  have hib : i < bs.length := by omega
  have hsplitA : as = as.take i ++ as.getD i 0 :: as.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i as]
    congr 1
    rw [List.drop_eq_getElem_cons hia]
    congr 1
    simp [List.getD, List.getElem?_eq_getElem hia]
  have hsplitB : bs = bs.take i ++ bs.getD i 0 :: bs.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i bs]
    congr 1
    rw [List.drop_eq_getElem_cons hib]
    congr 1
    simp [List.getD, List.getElem?_eq_getElem hib]
  have htakeEq : as.take i = bs.take i := by
    apply List.ext_getElem (by simp [List.length_take]; omega)
    intro j hj1 hj2
    simp only [List.length_take] at hj1
    have hja : j < as.length := by omega
    have hjb : j < bs.length := by omega
    rw [List.getElem_take, List.getElem_take]
    have := hpref j (by omega)
    simpa [List.getD, List.getElem?_eq_getElem hja,
      List.getElem?_eq_getElem hjb] using this
  have hdlen : (as.drop (i + 1)).length = (bs.drop (i + 1)).length := by
    simp [List.length_drop]; omega
  have hA := congrArg beBytesToNat hsplitA
  have hB := congrArg beBytesToNat hsplitB
  rw [beBytesToNat_append] at hA hB
  have hconsA : beBytesToNat (as.getD i 0 :: as.drop (i + 1))
      = (as.getD i 0).toNat * 256 ^ (as.drop (i + 1)).length
        + beBytesToNat (as.drop (i + 1)) := by
    show (as.drop (i + 1)).foldl _ (0 * 256 + (as.getD i 0).toNat) = _
    rw [beBytesToNat_foldl, Nat.zero_mul, Nat.zero_add]
  have hconsB : beBytesToNat (bs.getD i 0 :: bs.drop (i + 1))
      = (bs.getD i 0).toNat * 256 ^ (bs.drop (i + 1)).length
        + beBytesToNat (bs.drop (i + 1)) := by
    show (bs.drop (i + 1)).foldl _ (0 * 256 + (bs.getD i 0).toNat) = _
    rw [beBytesToNat_foldl, Nat.zero_mul, Nat.zero_add]
  have hbndA := beBytesToNat_bound (as.drop (i + 1))
  have hbndB := beBytesToNat_bound (bs.drop (i + 1))
  have hlenTail : (as.getD i 0 :: as.drop (i + 1)).length
      = (bs.getD i 0 :: bs.drop (i + 1)).length := by
    simp [List.length_drop]; omega
  rw [hconsA, hdlen] at hA
  rw [hconsB] at hB
  rw [htakeEq] at hA
  rw [hA, hB, hlenTail]
  rw [hdlen] at hbndA
  set T := 256 ^ (bs.drop (i + 1)).length with hT
  have hstep : (as.getD i 0).toNat * T + beBytesToNat (as.drop (i + 1))
      < (bs.getD i 0).toNat * T + beBytesToNat (bs.drop (i + 1)) := by
    have h1 : (as.getD i 0).toNat + 1 ≤ (bs.getD i 0).toNat := hlt
    calc (as.getD i 0).toNat * T + beBytesToNat (as.drop (i + 1))
        < (as.getD i 0).toNat * T + T := by omega
      _ = ((as.getD i 0).toNat + 1) * T := by
          rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (bs.getD i 0).toNat * T := Nat.mul_le_mul_right T h1
      _ ≤ (bs.getD i 0).toNat * T + beBytesToNat (bs.drop (i + 1)) :=
          Nat.le_add_right _ _
  have hll : (as.getD i 0 :: as.drop (i + 1)).length
      = (bs.getD i 0 :: bs.drop (i + 1)).length := hlenTail
  exact Nat.add_lt_add_left hstep _

/-- All bytes equal (equal lengths) means equal lists.  (Public: also
    consumed by `U256LtBeSAsm`.) -/
theorem bytes_eq_of_prefix_all (as bs : List (BitVec 8))
    (hlen : as.length = bs.length)
    (hpref : ∀ j, j < as.length → as.getD j 0 = bs.getD j 0) :
    as = bs := by
  apply List.ext_getElem hlen
  intro j hj1 hj2
  have := hpref j hj1
  simpa [List.getD, List.getElem?_eq_getElem hj1,
    List.getElem?_eq_getElem hj2] using this

-- ============================================================================
-- §2  The byte-walk scan loop (post-join region choice at the exits)
-- ============================================================================

section Scan

variable (aPtr bPtr outPtr ret : Word) (as bs os : List (BitVec 8))

/-- The `min` selector: pick `a` iff `a ≤ b` numerically (BE order). -/
private def minSel : Prop := beBytesToNat as ≤ beBytesToNat bs

private instance : Decidable (minSel as bs) := Nat.decLe _ _

/-- Shared pick-`a` exit segment (`mv x5, a0 ; j .copy`), entered with the
    selector KNOWN true. -/
private theorem pickA_spec (w : Word) (hcond : minSel as bs) :
    cpsTripleWithin 2 (0x80024dd0 : Word) (0x80024ddc : Word)
      (CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
      (((.x5 : Reg) ↦ᵣ w) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
      (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os) := by
  have hmv := liftCode (cr' := CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
    (mv_spec_gen_within .x5 .x10 aPtr w (0x80024dd0 : Word) (by decide))
    (by code_mem)
  rw [show (0x80024dd0 : Word) + 4 = (0x80024dd4 : Word) from by decide] at hmv
  have hjal := liftCode (cr' := CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
    (jal_x0_spec_gen_within (8 : BitVec 21) (0x80024dd4 : Word))
    (by code_mem)
  rw [show (0x80024dd4 : Word) + signExtend21 (8 : BitVec 21) = (0x80024ddc : Word)
    from by decide] at hjal
  have hmvF := cpsTripleWithin_frameR
    (((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
    (by pcf) hmv
  have hjalF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ aPtr) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
    (by pcf) hjal
  have hc := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [sepConj_emp_left']
      xperm_hyp hp) hmvF hjalF
  refine cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      rw [sepConj_emp_left'] at hq
      rw [if_pos hcond]
      xperm_hyp hq) hc

/-- Shared pick-`b` exit segment (`mv x5, a1`, falling into `.copy`),
    entered with the selector KNOWN false. -/
private theorem pickB_spec (w : Word) (hcond : ¬ minSel as bs) :
    cpsTripleWithin 1 (0x80024dd8 : Word) (0x80024ddc : Word)
      (CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
      (((.x5 : Reg) ↦ᵣ w) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
      (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os) := by
  have hmv := liftCode (cr' := CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
    (mv_spec_gen_within .x5 .x11 bPtr w (0x80024dd8 : Word) (by decide))
    (by code_mem)
  rw [show (0x80024dd8 : Word) + 4 = (0x80024ddc : Word) from by decide] at hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
    (by pcf) hmv
  refine cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      rw [if_neg hcond]
      xperm_hyp hq) hmvF

/-- **The byte-walk scan**: from the loop header with `i` bytes known
    equal, reach the copy entry with `x5` pinned to the SELECTED operand's
    base — the post-join region choice. -/
private theorem scanLoop_spec
    (hlenA : as.length = 32) (hlenB : bs.length = 32)
    (halignA : aPtr.toNat % 8 = 0) (halignB : bPtr.toNat % 8 = 0)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 → isValidByteAccess (aPtr + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 → isValidByteAccess (bPtr + BitVec.ofNat 64 k) = true)
    (M i : Nat) (hMi : i + M = 32)
    (hpref : ∀ j, j < i → as.getD j 0 = bs.getD j 0) :
    cpsTripleWithin (9 * M + 8) (0x80024dac : Word) (0x80024ddc : Word)
      (CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
      (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
      (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os) := by
  induction M generalizing i with
  | zero =>
      -- i = 32: header BEQ taken, all bytes equal → pick a.
      have hi32 : i = 32 := by omega
      subst hi32
      have hEq : as = bs := bytes_eq_of_prefix_all as bs (by omega)
        (fun j hj => hpref j (by omega))
      have hcond : minSel as bs := by unfold minSel; rw [hEq]
      have hbr := cpsBranchWithin_frameR
        (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        (by pcf)
        (cpsBranchWithin_extend_code
          (cr' := CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
          (h := beq_spec_gen_within .x5 .x31 (36 : BitVec 13)
            (BitVec.ofNat 64 32) (32 : Word) (0x80024dac : Word))
          (hmono := by code_mem))
      rw [show (0x80024dac : Word) + signExtend13 (36 : BitVec 13)
            = (0x80024dd0 : Word) from by decide,
          show (0x80024dac : Word) + 4 = (0x80024db0 : Word) from by decide] at hbr
      have hstation := retJoinStation_spec
        (cond := (BitVec.ofNat 64 32 = (32 : Word)))
        (PT := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 32) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) **
          ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        (PF := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 32) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) **
          ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        hbr
        (fun h hq => by xperm_hyp hq)
        (fun h hq => by xperm_hyp hq)
        (fun _ => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq)
          (pickA_spec aPtr bPtr outPtr ret as bs os (BitVec.ofNat 64 32) hcond))
        (fun hc => absurd (by decide : (BitVec.ofNat 64 32) = (32 : Word)) hc)
      exact cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun _ hq => hq)
        (cpsTripleWithin_mono_nSteps (by omega) hstation)
  | succ n ih =>
      have hiN : i < 32 := by omega
      set CR := CodeReq.ofProg (0x80024da4 : Word) u256Min_prog with hCR
      have hia : i < as.length := by omega
      have hib : i < bs.length := by omega
      set aByte := (as[i]'hia).zeroExtend 64 with haByte
      set bByte := (bs[i]'hib).zeroExtend 64 with hbByte
      have haBN : aByte.toNat = (as[i]'hia).toNat := by
        rw [haByte]
        show (BitVec.setWidth 64 _).toNat = _
        rw [BitVec.toNat_setWidth]
        have := (as[i]'hia).isLt
        omega
      have hbBN : bByte.toNat = (bs[i]'hib).toNat := by
        rw [hbByte]
        show (BitVec.setWidth 64 _).toNat = _
        rw [BitVec.toNat_setWidth]
        have := (bs[i]'hib).isLt
        omega
      have hgdA : as.getD i 0 = as[i]'hia := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia]
        rfl
      have hgdB : bs.getD i 0 = bs[i]'hib := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib]
        rfl
      -- peel this iteration's scratch values
      refine cpsTripleWithin_weaken
        (fun h hp => by
          simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
          xperm_hyp hp)
        (fun _ hq => hq)
        (cpsTripleWithin_peel_regOwns [.x6, .x7, .x28, .x29] (by decide)
          (P := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
            ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
            ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
            ((.x1 : Reg) ↦ᵣ ret) **
            bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          (fun vf => ?_))
      simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
      -- ---- the four body instructions ----
      have hadd6 := liftCode (cr' := CR)
        (add_spec_gen_within .x6 .x10 .x5 aPtr (BitVec.ofNat 64 i) (vf .x6)
          (0x80024db0 : Word) (by decide))
        (by rw [hCR]; code_mem)
      rw [show (0x80024db0 : Word) + 4 = (0x80024db4 : Word) from by decide] at hadd6
      have hadd7 := liftCode (cr' := CR)
        (add_spec_gen_within .x7 .x11 .x5 bPtr (BitVec.ofNat 64 i) (vf .x7)
          (0x80024db4 : Word) (by decide))
        (by rw [hCR]; code_mem)
      rw [show (0x80024db4 : Word) + 4 = (0x80024db8 : Word) from by decide] at hadd7
      have hlbuA := liftCode (cr' := CR)
        (bytesRegion_lbu_within .x28 .x6 aPtr (vf .x28) (0x80024db8 : Word)
          as i (by decide) halignA hia (by omega) (hvalidA i hiN))
        (by rw [hCR]; code_mem)
      rw [show (0x80024db8 : Word) + 4 = (0x80024dbc : Word) from by decide] at hlbuA
      have hlbuB := liftCode (cr' := CR)
        (bytesRegion_lbu_within .x29 .x7 bPtr (vf .x29) (0x80024dbc : Word)
          bs i (by decide) halignB hib (by omega) (hvalidB i hiN))
        (by rw [hCR]; code_mem)
      rw [show (0x80024dbc : Word) + 4 = (0x80024dc0 : Word) from by decide] at hlbuB
      -- ---- frames + chain of the body ----
      have hadd6F := cpsTripleWithin_frameR
        ((.x7 ↦ᵣ vf .x7) ** (.x28 ↦ᵣ vf .x28) ** (.x29 ↦ᵣ vf .x29) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        (by pcf) hadd6
      have hadd7F := cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) ** (.x28 ↦ᵣ vf .x28) **
          (.x29 ↦ᵣ vf .x29) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        (by pcf) hadd7
      have hlbuAF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          (.x29 ↦ᵣ vf .x29) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion bPtr bs ** bytesRegion outPtr os)
        (by pcf) hlbuA
      have hlbuBF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x28 ↦ᵣ aByte) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion outPtr os)
        (by pcf) hlbuB
      have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hadd6F hadd7F
      have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hc1 hlbuAF
      have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
        hc2 hlbuBF
      -- ---- header BEQ (never taken at i < 32) ----
      have hneHdr : ¬ ((BitVec.ofNat 64 i : Word) = (32 : Word)) := by
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show ((32 : Word)).toNat = 32 from rfl] at this
        omega
      have hbrHdr := cpsBranchWithin_frameR
        ((.x6 ↦ᵣ vf .x6) ** (.x7 ↦ᵣ vf .x7) ** (.x28 ↦ᵣ vf .x28) **
          (.x29 ↦ᵣ vf .x29) **
          ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
          ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        (by pcf)
        (cpsBranchWithin_extend_code (cr' := CR)
          (h := beq_spec_gen_within .x5 .x31 (36 : BitVec 13)
            (BitVec.ofNat 64 i) (32 : Word) (0x80024dac : Word))
          (hmono := by rw [hCR]; code_mem))
      rw [show (0x80024dac : Word) + signExtend13 (36 : BitVec 13)
            = (0x80024dd0 : Word) from by decide,
          show (0x80024dac : Word) + 4 = (0x80024db0 : Word) from by decide] at hbrHdr
      -- ---- station 1: BLTU x28 x29 → pick a ----
      have hbr1 := cpsBranchWithin_frameR
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        (by pcf)
        (cpsBranchWithin_extend_code (cr' := CR)
          (h := bltu_spec_gen_within .x28 .x29 (16 : BitVec 13) aByte bByte
            (0x80024dc0 : Word))
          (hmono := by rw [hCR]; code_mem))
      rw [show (0x80024dc0 : Word) + signExtend13 (16 : BitVec 13)
            = (0x80024dd0 : Word) from by decide,
          show (0x80024dc0 : Word) + 4 = (0x80024dc4 : Word) from by decide] at hbr1
      -- ---- station 2: BLTU x29 x28 → pick b ----
      have hbr2 := cpsBranchWithin_frameR
        (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        (by pcf)
        (cpsBranchWithin_extend_code (cr' := CR)
          (h := bltu_spec_gen_within .x29 .x28 (20 : BitVec 13) bByte aByte
            (0x80024dc4 : Word))
          (hmono := by rw [hCR]; code_mem))
      rw [show (0x80024dc4 : Word) + signExtend13 (20 : BitVec 13)
            = (0x80024dd8 : Word) from by decide,
          show (0x80024dc4 : Word) + 4 = (0x80024dc8 : Word) from by decide] at hbr2
      -- ---- continue segment: ADDI + JAL back, then the IH ----
      have haddi := liftCode (cr' := CR)
        (addi_spec_gen_same_within .x5 (BitVec.ofNat 64 i) (1 : BitVec 12)
          (0x80024dc8 : Word) (by decide))
        (by rw [hCR]; code_mem)
      rw [show (BitVec.ofNat 64 i : Word) + signExtend12 (1 : BitVec 12)
            = BitVec.ofNat 64 (i + 1) from by
          rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            show ((1 : Word)).toNat = 1 from rfl]
          omega,
          show (0x80024dc8 : Word) + 4 = (0x80024dcc : Word) from by decide] at haddi
      have hjal := liftCode (cr' := CR)
        (jal_x0_spec_gen_within (-32 : BitVec 21) (0x80024dcc : Word))
        (by rw [hCR]; code_mem)
      rw [show (0x80024dcc : Word) + signExtend21 (-32 : BitVec 21)
            = (0x80024dac : Word) from by decide] at hjal
      -- ---- continue segment (both bytes equal): ADDI ; JAL ; IH ----
      have hcont : ¬ BitVec.ult aByte bByte → ¬ BitVec.ult bByte aByte →
          cpsTripleWithin (9 * n + 10) (0x80024dc8 : Word)
            (0x80024ddc : Word) CR
            ((.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
            (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os) := by
        intro hnAB hnBA
        have hEqByte : as[i]'hia = bs[i]'hib := by
          apply BitVec.eq_of_toNat_eq
          have h1 : ¬ aByte.toNat < bByte.toNat := by
            intro hlt
            exact hnAB (by simp [BitVec.ult, decide_eq_true_eq]; omega)
          have h2 : ¬ bByte.toNat < aByte.toNat := by
            intro hlt
            exact hnBA (by simp [BitVec.ult, decide_eq_true_eq]; omega)
          omega
        have hpref' : ∀ j, j < i + 1 → as.getD j 0 = bs.getD j 0 := by
          intro j hj
          by_cases hji : j < i
          · exact hpref j hji
          · have : j = i := by omega
            subst this
            rw [hgdA, hgdB, hEqByte]
        have hih := ih (i + 1) (by omega) hpref'
        have haddiF := cpsTripleWithin_frameR
          ((.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
            (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
            (.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
            ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
            ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
            ((.x1 : Reg) ↦ᵣ ret) **
            bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          (by pcf) haddi
        have hjalF := cpsTripleWithin_frameR
          (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
            (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
            (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
            (.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
            ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
            ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
            ((.x1 : Reg) ↦ᵣ ret) **
            bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          (by pcf) hjal
        have hj1 := cpsTripleWithin_seq_perm_same_cr
          (fun h hp => by
            rw [sepConj_emp_left']
            xperm_hyp hp) haddiF hjalF
        have hj2 := cpsTripleWithin_seq_perm_same_cr
          (fun h hp => by
            rw [sepConj_emp_left'] at hp
            have hp1 : ((.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
                ((.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
                  ((.x28 ↦ᵣ aByte) ** ((.x29 ↦ᵣ bByte) **
                    ((((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
                     ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
                     ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                     ((.x1 : Reg) ↦ᵣ ret) **
                     bytesRegion aPtr as ** bytesRegion bPtr bs **
                     bytesRegion outPtr os)))))) h := by
              xperm_hyp hp
            have hp2 := sepConj_mono (regIs_to_regOwn .x6 _)
              (sepConj_mono (regIs_to_regOwn .x7 _)
                (sepConj_mono (regIs_to_regOwn .x28 _)
                  (sepConj_mono (regIs_to_regOwn .x29 _)
                    (fun _ hh => hh)))) h hp1
            xperm_hyp hp2) hj1 hih
        exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (by omega) hj2)
      -- ---- station 2: BLTU x29 x28 → pick b ----
      have hstation2 : ¬ BitVec.ult aByte bByte →
          cpsTripleWithin (1 + (9 * n + 10)) (0x80024dc4 : Word)
            (0x80024ddc : Word) CR
            ((.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
            (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os) := by
        intro hnAB
        have hst := retJoinStation_spec
          (cond := BitVec.ult bByte aByte)
          (PT := (.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          (PF := (.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          hbr2
          (fun h hq => by xperm_hyp hq)
          (fun h hq => by xperm_hyp hq)
          (fun hc => by
            have hltN : (bs[i]'hib).toNat < (as[i]'hia).toNat := by
              have hc' : bByte.toNat < aByte.toNat := by
                simpa [BitVec.ult, decide_eq_true_eq] using hc
              omega
            have hncond : ¬ minSel as bs := by
              unfold minSel
              have := beBytesToNat_lt_of_prefix_lt bs as (by omega) i hib
                (fun j hj => (hpref j hj).symm)
                (by rw [hgdA, hgdB]; omega)
              omega
            exact cpsTripleWithin_weaken
              (fun h hp => by
            have hp1 : ((.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
                ((.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
                  ((.x28 ↦ᵣ aByte) ** ((.x29 ↦ᵣ bByte) **
                    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
                     ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
                     ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                     ((.x1 : Reg) ↦ᵣ ret) **
                     bytesRegion aPtr as ** bytesRegion bPtr bs **
                     bytesRegion outPtr os))))) h := by
              xperm_hyp hp
            have hp2 := sepConj_mono (regIs_to_regOwn .x6 _)
              (sepConj_mono (regIs_to_regOwn .x7 _)
                (sepConj_mono (regIs_to_regOwn .x28 _)
                  (sepConj_mono (regIs_to_regOwn .x29 _)
                    (fun _ hh => hh)))) h hp1
            xperm_hyp hp2)
              (fun _ hq => hq)
              (cpsTripleWithin_mono_nSteps (nSteps' := 9 * n + 10) (by omega)
                (pickB_spec aPtr bPtr outPtr ret as bs os
                  (BitVec.ofNat 64 i) hncond)))
          (fun hc => hcont hnAB hc)
        exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) hst
      -- ---- station 1: BLTU x28 x29 → pick a ----
      have hstation1 : cpsTripleWithin (1 + (1 + (9 * n + 10))) (0x80024dc0 : Word)
          (0x80024ddc : Word) CR
          ((.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os) := by
        have hst := retJoinStation_spec
          (cond := BitVec.ult aByte bByte)
          (PT := (.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          (PF := (.x28 ↦ᵣ aByte) ** (.x29 ↦ᵣ bByte) **
          ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          (.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
          (.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          hbr1
          (fun h hq => by xperm_hyp hq)
          (fun h hq => by xperm_hyp hq)
          (fun hc => by
            have hltN : (as[i]'hia).toNat < (bs[i]'hib).toNat := by
              have hc' : aByte.toNat < bByte.toNat := by
                simpa [BitVec.ult, decide_eq_true_eq] using hc
              omega
            have hcond : minSel as bs := by
              unfold minSel
              exact Nat.le_of_lt (beBytesToNat_lt_of_prefix_lt as bs (by omega)
                i hia hpref (by rw [hgdA, hgdB]; omega))
            exact cpsTripleWithin_weaken
              (fun h hp => by
            have hp1 : ((.x6 ↦ᵣ (aPtr + BitVec.ofNat 64 i)) **
                ((.x7 ↦ᵣ (bPtr + BitVec.ofNat 64 i)) **
                  ((.x28 ↦ᵣ aByte) ** ((.x29 ↦ᵣ bByte) **
                    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
                     ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
                     ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
                     ((.x1 : Reg) ↦ᵣ ret) **
                     bytesRegion aPtr as ** bytesRegion bPtr bs **
                     bytesRegion outPtr os))))) h := by
              xperm_hyp hp
            have hp2 := sepConj_mono (regIs_to_regOwn .x6 _)
              (sepConj_mono (regIs_to_regOwn .x7 _)
                (sepConj_mono (regIs_to_regOwn .x28 _)
                  (sepConj_mono (regIs_to_regOwn .x29 _)
                    (fun _ hh => hh)))) h hp1
            xperm_hyp hp2)
              (fun _ hq => hq)
              (cpsTripleWithin_mono_nSteps (nSteps' := 1 + (9 * n + 10)) (by omega)
                (pickA_spec aPtr bPtr outPtr ret as bs os
                  (BitVec.ofNat 64 i) hcond)))
          (fun hc => hstation2 hc)
        exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) hst
      -- ---- body ; station 1 ----
      have hbody : cpsTripleWithin (9 * n + 16) (0x80024db0 : Word)
          (0x80024ddc : Word) CR
          (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
            (.x6 ↦ᵣ vf .x6) ** (.x7 ↦ᵣ vf .x7) **
            (.x28 ↦ᵣ vf .x28) ** (.x29 ↦ᵣ vf .x29) **
            ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
            ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
            ((.x1 : Reg) ↦ᵣ ret) **
            bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
          (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
          ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
          ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
          ((.x1 : Reg) ↦ᵣ ret) **
          regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os) := by
        refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq)
          (cpsTripleWithin_mono_nSteps (by omega)
            (cpsTripleWithin_seq_perm_same_cr
              (fun _ hp => by xperm_hyp hp) hc3 hstation1))
      -- ---- header station ----
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq)
        (cpsTripleWithin_mono_nSteps (by omega)
          (retJoinStation_spec
            (cond := ((BitVec.ofNat 64 i : Word) = (32 : Word)))
            (PT := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
              (.x6 ↦ᵣ vf .x6) ** (.x7 ↦ᵣ vf .x7) **
              (.x28 ↦ᵣ vf .x28) ** (.x29 ↦ᵣ vf .x29) **
              ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
              ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
              ((.x1 : Reg) ↦ᵣ ret) **
              bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
            (PF := ((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
              (.x6 ↦ᵣ vf .x6) ** (.x7 ↦ᵣ vf .x7) **
              (.x28 ↦ᵣ vf .x28) ** (.x29 ↦ᵣ vf .x29) **
              ((.x31 : Reg) ↦ᵣ (32 : Word)) ** ((.x10 : Reg) ↦ᵣ aPtr) **
              ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
              ((.x1 : Reg) ↦ᵣ ret) **
              bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
            hbrHdr
            (fun h hq => by xperm_hyp hq)
            (fun h hq => by xperm_hyp hq)
            (fun hc => absurd hc hneHdr)
            (fun _ => hbody)))

end Scan

-- ============================================================================
-- §3  The whole routine
-- ============================================================================

/-- **`u256_min` at its linked address** (genuine post): the 32-byte output
    is byte-for-byte the numerically-smaller big-endian operand (`a` on
    ties), both inputs untouched; `x5` still holds the selected base. -/
theorem u256Min_spec (aPtr bPtr outPtr ret : Word) (as bs os : List (BitVec 8))
    (hlenA : as.length = 32) (hlenB : bs.length = 32) (hlenO : os.length = 32)
    (halignA : aPtr.toNat % 8 = 0) (halignB : bPtr.toNat % 8 = 0)
    (hovA : aPtr.toNat + 32 < 2 ^ 64) (hovB : bPtr.toNat + 32 < 2 ^ 64)
    (hvalidA : ∀ k, k < 32 → isValidByteAccess (aPtr + BitVec.ofNat 64 k) = true)
    (hvalidB : ∀ k, k < 32 → isValidByteAccess (bPtr + BitVec.ofNat 64 k) = true)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 308 (0x80024da4 : Word) ret
      (CodeReq.ofProg (0x80024da4 : Word) u256Min_prog)
      (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x31 **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ bPtr) **
        ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x5 : Reg) ↦ᵣ (if beBytesToNat as ≤ beBytesToNat bs then aPtr else bPtr)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        ((.x31 : Reg) ↦ᵣ (32 : Word)) **
        bytesRegion aPtr as ** bytesRegion bPtr bs **
        bytesRegion outPtr
          (if beBytesToNat as ≤ beBytesToNat bs then as else bs)) := by
  set CR := CodeReq.ofProg (0x80024da4 : Word) u256Min_prog with hCR
  -- ---- init: li x5, 0 ; li x31, 32 ----
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_own_within .x5 (0 : Word) (0x80024da4 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x80024da4 : Word) + 4 = (0x80024da8 : Word) from by decide,
      show (0 : Word) = BitVec.ofNat 64 0 from rfl] at hli5
  have hli31 := liftCode (cr' := CR)
    (li_spec_gen_own_within .x31 (32 : Word) (0x80024da8 : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x80024da8 : Word) + 4 = (0x80024dac : Word) from by decide] at hli31
  -- ---- the byte-walk scan ----
  have hloop := scanLoop_spec aPtr bPtr outPtr ret as bs os
    hlenA hlenB halignA halignB hovA hovB hvalidA hvalidB 32 0 (by omega)
    (fun j hj => absurd hj (by omega))
  -- ---- the dynamically-selected copy tail (the combinator, per case) ----
  have hcopy : cpsTripleWithin 8 (0x80024ddc : Word) (0x80024dfc : Word) CR
      ((((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
        ((.x12 : Reg) ↦ᵣ outPtr) **
        bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
        ** regOwn .x6)
      ((((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
        ((.x12 : Reg) ↦ᵣ outPtr) **
        bytesRegion aPtr as ** bytesRegion bPtr bs **
        bytesRegion outPtr (if minSel as bs then as else bs))
        ** regOwn .x6) := by
    apply cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
    intro tv
    by_cases hc : minSel as bs
    · rw [if_pos hc, if_pos hc]
      have h := cpsTripleWithin_extend_code
        (hmono := CodeReq.ofProg_mono_sub (0x80024da4 : Word) (0x80024ddc : Word)
          u256Min_prog (dwordCopyProgFrom .x5 .x12 .x6 0 4) 14
          (by decide) (by decide) (by decide) (by decide))
        (selectedDwordCopy_spec .x5 .x12 .x6 (by decide) aPtr outPtr tv as os
          0 4 (by omega) (by omega) (by decide) (0x80024ddc : Word))
      rw [show (0x80024ddc : Word) + BitVec.ofNat 64 (4 * (2 * 4))
            = (0x80024dfc : Word) from by decide,
          copyDwords_covers as os 4 (by omega) (by omega)] at h
      have hF := cpsTripleWithin_frameR (bytesRegion bPtr bs) (by pcf) h
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) hF
    · rw [if_neg hc, if_neg hc]
      have h := cpsTripleWithin_extend_code
        (hmono := CodeReq.ofProg_mono_sub (0x80024da4 : Word) (0x80024ddc : Word)
          u256Min_prog (dwordCopyProgFrom .x5 .x12 .x6 0 4) 14
          (by decide) (by decide) (by decide) (by decide))
        (selectedDwordCopy_spec .x5 .x12 .x6 (by decide) bPtr outPtr tv bs os
          0 4 (by omega) (by omega) (by decide) (0x80024ddc : Word))
      rw [show (0x80024ddc : Word) + BitVec.ofNat 64 (4 * (2 * 4))
            = (0x80024dfc : Word) from by decide,
          copyDwords_covers bs os 4 (by omega) (by omega)] at h
      have hF := cpsTripleWithin_frameR (bytesRegion aPtr as) (by pcf) h
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq) hF
  -- ---- epilogue: li a0, 0 ; ret ----
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x10 aPtr (0 : Word) (0x80024dfc : Word) (by decide))
    (by rw [hCR]; code_mem)
  rw [show (0x80024dfc : Word) + 4 = (0x80024e00 : Word) from by decide] at hli10
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (0x80024e00 : Word) ret)
    (by rw [hCR]; code_mem)
  rw [halignRet] at hret
  -- ---- frames + chain ----
  have hli5F := cpsTripleWithin_frameR
    (regOwn .x31 ** ((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x12 : Reg) ↦ᵣ outPtr) ** ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
    (by pcf) hli5
  have hli31F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ BitVec.ofNat 64 0) ** ((.x10 : Reg) ↦ᵣ aPtr) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs ** bytesRegion outPtr os)
    (by pcf) hli31
  have hcopyF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ aPtr) ** ((.x11 : Reg) ↦ᵣ bPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29)
    (by pcf) hcopy
  have hli10F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x31 : Reg) ↦ᵣ (32 : Word)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs **
      bytesRegion outPtr (if minSel as bs then as else bs))
    (by pcf) hli10
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ (if minSel as bs then aPtr else bPtr)) **
      ((.x11 : Reg) ↦ᵣ bPtr) ** ((.x12 : Reg) ↦ᵣ outPtr) **
      ((.x31 : Reg) ↦ᵣ (32 : Word)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      bytesRegion aPtr as ** bytesRegion bPtr bs **
      bytesRegion outPtr (if minSel as bs then as else bs))
    (by pcf) hret
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hli5F hli31F
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c1 hloop
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c2 hcopyF
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c3 hli10F
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c4 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) c5)
  unfold minSel at hq
  xperm_hyp hq

#print axioms u256Min_spec

end U256MinSAsm

end EvmAsm.Codegen
