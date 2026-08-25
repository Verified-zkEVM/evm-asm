/-
  Arena/window contracts for `rlp_encode_uint_be`.

  The ordinary whole-routine triple in `RlpEncodeUintBeComposeSAsm` owns an
  output region whose base is the logical pointer.  Production callers instead
  hand the encoder a shared aligned arena and put the logical output at an
  arbitrary byte offset.  This module carries the same three path proofs over
  that arena without changing the emitted program.
-/

import EvmAsm.Codegen.Programs.RlpEncodeUintBeComposeSAsm

namespace EvmAsm.Codegen
namespace RlpEncodeUintBeSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Rv64.RLP (copyN copyN_eq_append word_ofNat_add_one)

private theorem setBytes_eq_append (bs ns : List Byte) (i : Nat)
    (hfit : i + ns.length ≤ bs.length) :
    setBytes bs i ns = bs.take i ++ ns ++ bs.drop (i + ns.length) := by
  have hleft : (setBytes bs i ns).take i = bs.take i :=
    setBytes_take_of_ge ns bs i i (Nat.le_refl _)
  have hmid : ((setBytes bs i ns).drop i).take ns.length = ns :=
    window_readback bs ns i hfit
  have hright : (setBytes bs i ns).drop (i + ns.length) =
      bs.drop (i + ns.length) :=
    setBytes_drop_of_le ns bs i (i + ns.length) (by omega)
  rw [← List.take_append_drop i (setBytes bs i ns)]
  rw [hleft, ← List.take_append_drop ns.length ((setBytes bs i ns).drop i)]
  rw [hmid, List.drop_drop, hright]
  simp [List.append_assoc]

private theorem reub_header_copy_result (arenaBytes xs : List Byte)
    (off d n : Nat) (hdr : Byte) (hn : xs.length = n)
    (hfit : off + (1 + (n - d)) ≤ arenaBytes.length)
    (hd : d ≤ n) :
    copyN (arenaBytes.set off hdr) xs (off + 1) d (n - d) =
      setBytes arenaBytes off (hdr :: xs.drop d) := by
  have hsetFit : off + (hdr :: xs.drop d).length ≤ arenaBytes.length := by
    simpa [List.length_drop, hn, Nat.sub_add_cancel hd, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using hfit
  have hofflen : off + 1 + (n - d) = off + (n - d + 1) := by omega
  rw [copyN_eq_append _ _ _ _ _ (by rw [List.length_set]; omega)
    (by simp [hn]; omega), setBytes_eq_append _ _ _ hsetFit]
  have hoff : off < arenaBytes.length := by omega
  have hmin : min off arenaBytes.length = off := Nat.min_eq_left (by omega)
  rw [List.set_eq_take_cons_drop _ hoff, List.take_append, List.drop_append]
  simp only [List.length_take, hmin]
  have htake : List.take (off + 1) (List.take off arenaBytes) =
      List.take off arenaBytes :=
    List.take_of_length_le (by simp [hmin])
  have hdrop1 : List.drop (off + 1 + (n - d)) (List.take off arenaBytes) = [] :=
    List.drop_eq_nil_of_le (by simp [hmin]; omega)
  have hdrop2 : List.drop (off + 1 + (n - d) - off)
      (hdr :: List.drop (off + 1) arenaBytes) =
      List.drop (off + (n - d + 1)) arenaBytes := by
    rw [show off + 1 + (n - d) - off = (n - d) + 1 by omega,
      List.drop_succ_cons, List.drop_drop]
    exact congrArg (fun q => List.drop q arenaBytes) hofflen
  rw [htake, hdrop1, hdrop2]
  have hsrc : List.take (n - d) (xs.drop d) = xs.drop d := by
    rw [List.take_of_length_le]
    simp [hn]
  rw [hsrc]
  have hhdrtake : List.take (off + 1 - off)
      (hdr :: List.drop (off + 1) arenaBytes) = [hdr] := by
    rw [show off + 1 - off = 1 by omega, List.take_cons (by decide),
      List.take_zero]
  rw [hhdrtake]
  have hlenrhs : (hdr :: xs.drop d).length = 1 + (n - d) := by
    simp [List.length_drop, hn]
    omega
  rw [hlenrhs]
  have hnorm : off + (1 + (n - d)) = off + (n - d + 1) := by omega
  rw [hnorm]
  simp [List.append_assoc]

theorem reubAbiArenaPre_zero (srcPtr outPtr raVal : Word)
    (xs oldOut : List Byte) (n : Nat) (v5 v6 v28 v29 v30 v31 : Word) :
    reubAbiArenaPre srcPtr outPtr raVal xs oldOut 0 n v5 v6 v28 v29 v30 v31 =
      reubAbiPre srcPtr outPtr raVal xs oldOut n v5 v6 v28 v29 v30 v31 := by
  simp [reubAbiArenaPre, reubAbiPre]

theorem reubAbiArenaPost_zero (srcPtr outPtr raVal : Word)
    (xs oldOut : List Byte) (n : Nat) (hxs : xs.length = n)
    (hn : 0 + (reubOut xs).length ≤ oldOut.length) :
    reubAbiArenaPost srcPtr outPtr raVal xs oldOut 0 =
      reubAbiPost srcPtr outPtr raVal xs oldOut n := by
  unfold reubAbiArenaPost reubAbiPost
  rw [setBytes_eq_append oldOut (reubOut xs) 0 (by simpa using hn)]
  rw [hxs]
  simp

/-! The arena proof below is split into the same raw/small/header cases as the
    ordinary composition.  The strip and dispatch blocks are framed with an
    empty logical output region, since they do not touch output; the write and
    copy blocks use the arena-specialized low-level contracts. -/

set_option maxRecDepth 8000 in
theorem reub_spec_arena_within (srcPtr arenaPtr raVal : Word)
    (v5 v6 v28 v29 v30 v31 : Word) (xs arenaBytes : List Byte)
    (off n : Nat) (hn : xs.length = n)
    (hdom : n - reubZeros xs 0 n ≤ 55)
    (hfit : off + n + 1 ≤ arenaBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hbase_align : arenaPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hover : arenaPtr.toNat + (off + n + 1) < 2 ^ 64)
    (hsvalid : ∀ k, k < n →
      isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ k, k < n + 1 →
      isValidByteAccess (arenaPtr + BitVec.ofNat 64 (off + k)) = true) :
    cpsTripleWithin (n * 6 + 7 * (n - reubZeros xs 0 n) + 17)
      reubBase (raVal &&& ~~~1) reubCode
      (reubAbiArenaPre srcPtr arenaPtr raVal xs arenaBytes off n
        v5 v6 v28 v29 v30 v31)
      (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
  have hzle : reubZeros xs 0 n ≤ n := reubZeros_le xs 0 n
  have hhoff : off < arenaBytes.length := by omega
  have hvalid0 : isValidByteAccess (arenaPtr + BitVec.ofNat 64 off) = true :=
    hvalid 0 (by omega)
  let F : Assertion :=
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
    ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion arenaPtr arenaBytes
  have hpro0 := reubPrologue srcPtr (arenaPtr + BitVec.ofNat 64 off) raVal
    v5 v6 v28 xs [] n
  have hpro := cpsTripleWithin_frameR F (by unfold F; pcFree) hpro0
  by_cases hz : reubZeros xs 0 n = n
  · have hall : ∀ b ∈ xs, b = 0 :=
      (reubStrip_eq_nil_iff xs).1 (reubStrip_nil_of_zeros_eq xs n hn hz)
    have hout : reubOut xs = [BitVec.ofNat 8 0x80] :=
      reubOut_of_all_zero xs hall
    have hloop0 := reubStripLoop srcPtr (arenaPtr + BitVec.ofNat 64 off)
      raVal xs [] n (by omega) (by omega) hsalign hsover hsvalid
    have hloop := cpsBranchWithin_frameR
      (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)
      (by unfold F; pcFree) hloop0
    have hexh := cpsBranchWithin_ntakenPath hloop (fun _ hQt => by
      obtain ⟨_, _, _, _, hBreak, _⟩ := hQt
      obtain ⟨d, hd⟩ := hBreak
      have hpure := ((sepConj_pure_right _).1 hd).2
      omega)
    have htail : ∀ w28, cpsTripleWithin 4 (reubBase + 32)
        (raVal &&& ~~~1) reubCode
        ((((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) **
          ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
          ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion srcPtr xs **
          ((.x10 : Reg) ↦ᵣ srcPtr) **
          ((.x12 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 off)) **
          ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion arenaPtr arenaBytes) ** ((.x28 : Reg) ↦ᵣ w28))
        (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
      intro w28
      have ht := reubEmptyTail_arena arenaPtr raVal w28 srcPtr arenaBytes off
        hbase_align hhoff (by omega) hvalid0
      have htF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) **
         ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
         ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
         ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion srcPtr xs **
         ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (by pcFree) ht
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) htF
      · xperm_hyp hp
      · unfold reubAbiArenaPost
        rw [hout, setBytes_singleton]
        simp only [hn]
        have hp' : (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 n)) **
            ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - n)) **
            ((.x28 : Reg) ↦ᵣ (128 : Word)) **
            ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
            ((.x31 : Reg) ↦ᵣ v31) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
            ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion srcPtr xs **
            ((.x12 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 off)) **
            ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion arenaPtr (arenaBytes.set off (BitVec.ofNat 8 0x80))) h := by
          xperm_hyp hp
        exact scratch_to_own_arena srcPtr arenaPtr raVal xs
          (arenaBytes.set off (BitVec.ofNat 8 0x80)) off n (1 : Word)
          (srcPtr + BitVec.ofNat 64 n) (BitVec.ofNat 64 (n - n))
          (128 : Word) v29 v30 v31 h hp'
    have hmid := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      unfold reubExhPost reubInvCore reubStable reubAmb at hp
      simp only [bytesRegion_nil, sepConj_emp_right'] at hp
      have hp1 := sepConj_mono_left
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp
      have hp2 := by simpa only [bytesRegion_nil, sepConj_emp_right'] using hp1
      xperm_hyp hp2) hexh
      (cpsTripleWithin_of_forall_regIs_to_regOwn (fun w28 => htail w28))
    have hfull := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      unfold F at hp ⊢
      xperm_hyp hp) hpro hmid
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hfull)
    · unfold reubAbiArenaPre at hp
      simp only [bytesRegion_nil, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp
  · have hd : reubZeros xs 0 n < n := by omega
    have hdlen : reubZeros xs 0 n < xs.length := by omega
    have hstrip : reubStrip xs = xs.drop (reubZeros xs 0 n) :=
      reubStrip_eq_drop_zeros xs n hn
    have hLlen : (reubStrip xs).length = n - reubZeros xs 0 n :=
      reubStrip_length_eq xs n hn
    have hbeq : ∀ b, reubStrip xs = [b] →
        n - reubZeros xs 0 n = 1 ∧ (xs[reubZeros xs 0 n]'hdlen) = b := by
      intro b hb
      have h1 : n - reubZeros xs 0 n = 1 := by rw [← hLlen, hb]; rfl
      refine ⟨h1, ?_⟩
      have hxb := drop_eq_singleton xs (reubZeros xs 0 n) hdlen (by omega)
      have heq : xs.drop (reubZeros xs 0 n) = [b] := by rw [← hstrip]; exact hb
      rw [hxb] at heq
      simpa using heq
    by_cases h1 : (n - reubZeros xs 0 n) = 1
    · by_cases hsmall : (xs[reubZeros xs 0 n]'hdlen).toNat < 128
      · exact cpsTripleWithin_mono_nSteps (by omega)
          (reub_spec_arena_single_small_aux srcPtr arenaPtr raVal
            v5 v6 v28 v29 v30 v31 xs arenaBytes off n hn (by omega)
            hd h1 hdlen hsmall (by omega) hsalign hbase_align hsover
            (by omega) hsvalid hvalid)
      · exact reub_spec_arena_header_aux srcPtr arenaPtr raVal
          v5 v6 v28 v29 v30 v31 xs arenaBytes off n hn (by omega) hd hdom
          (by
            intro b hb
            obtain ⟨_, hbyte⟩ := hbeq b hb
            rw [← hbyte]
            omega)
          hfit
          hsalign hbase_align hsover hover hsvalid hvalid
    · exact reub_spec_arena_header_aux srcPtr arenaPtr raVal
        v5 v6 v28 v29 v30 v31 xs arenaBytes off n hn (by omega) hd hdom
        (by
          intro b hb
          obtain ⟨h1', _⟩ := hbeq b hb
          omega)
        hfit
        hsalign hbase_align hsover hover hsvalid hvalid
where
  reub_spec_arena_single_small_aux (srcPtr arenaPtr raVal : Word)
      (v5 v6 v28 v29 v30 v31 : Word) (xs arenaBytes : List Byte)
      (off n : Nat) (hn : xs.length = n) (hn64 : n < 2 ^ 64)
      (hd : reubZeros xs 0 n < n)
      (hL : n - reubZeros xs 0 n = 1)
      (hdlen : reubZeros xs 0 n < xs.length)
      (hsmall : (xs[reubZeros xs 0 n]'hdlen).toNat < 128)
      (hfit : off + 1 ≤ arenaBytes.length)
      (hsalign : srcPtr.toNat % 8 = 0) (hbase_align : arenaPtr.toNat % 8 = 0)
      (hsover : srcPtr.toNat + n < 2 ^ 64)
      (hover : arenaPtr.toNat + off < 2 ^ 64)
      (hsvalid : ∀ k, k < n →
        isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
      (hvalid : ∀ k, k < n + 1 →
        isValidByteAccess (arenaPtr + BitVec.ofNat 64 (off + k)) = true) :
      cpsTripleWithin (n * 6 + 12) reubBase (raVal &&& ~~~1) reubCode
        (reubAbiArenaPre srcPtr arenaPtr raVal xs arenaBytes off n
          v5 v6 v28 v29 v30 v31)
        (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
    set d := reubZeros xs 0 n with hdef
    set b := xs[d]'hdlen with hbdef
    have hstrip : reubStrip xs = [b] := by
      rw [reubStrip_eq_drop_zeros xs n hn, ← hdef]
      exact drop_eq_singleton xs d hdlen (by omega)
    have hout : reubOut xs = [b] :=
      reubOut_single_small xs b hstrip (by omega)
    have hlen1 : (reubOut xs).length = 1 := by rw [hout]; rfl
    let F : Assertion :=
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion arenaPtr arenaBytes
    have hF : F.pcFree := by unfold F; pcFree
    have hpro0 := reubPrologue srcPtr (arenaPtr + BitVec.ofNat 64 off)
      raVal v5 v6 v28 xs [] n
    have hpro := cpsTripleWithin_frameR F hF hpro0
    have hloop0 := reubStripLoop srcPtr (arenaPtr + BitVec.ofNat 64 off)
      raVal xs [] n (by omega) hn64 hsalign hsover hsvalid
    have hloop := cpsBranchWithin_frameR
      (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)
      (by unfold F; pcFree) hloop0
    have hbrk := cpsBranchWithin_takenPath hloop (fun _ hQf => by
      obtain ⟨_, _, _, _, hExh, _⟩ := hQf
      unfold reubExhPost at hExh
      have hpure := ((sepConj_pure_right _).1 hExh).2
      omega)
    have htail : ∀ w28, cpsTripleWithin 9 (reubBase + 48)
        (raVal &&& ~~~1) reubCode
        ((((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
          ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
          ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion srcPtr xs **
          ((.x10 : Reg) ↦ᵣ srcPtr) **
          ((.x12 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 off)) **
          ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion arenaPtr arenaBytes) ** ((.x28 : Reg) ↦ᵣ w28))
        (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
      intro w28
      have hdisp := reubDispSmallSingle srcPtr (arenaPtr + BitVec.ofNat 64 off)
        raVal xs [] n d w28 v29 v30 v31 hdlen hL hsmall hsalign (by omega)
        (hsvalid d (by omega))
      have hdispF := cpsTripleWithin_frameR
        (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion arenaPtr arenaBytes)
        (by pcFree) hdisp
      have hsing := reubSingleTail_arena arenaPtr raVal srcPtr b
        arenaBytes off hbase_align (by omega) (by omega)
        (hvalid 0 (by omega))
      have hsingF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
         ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x30 : Reg) ↦ᵣ (128 : Word)) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion srcPtr xs **
         ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcFree) hsing
      have hchain := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          simp only [reubSinglePre, reubAmb, bytesRegion_nil,
            sepConj_emp_right'] at hp
          xperm_hyp hp) hdispF hsingF
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hchain
      · simp only [reubDispPre, reubAmb, bytesRegion_nil,
          sepConj_emp_right'] at hp ⊢
        xperm_hyp hp
      · unfold reubAbiArenaPost
        rw [hlen1, hout, setBytes_singleton]
        simp only [hn]
        refine scratch_to_own_arena srcPtr arenaPtr raVal xs
          (arenaBytes.set off b) off n (1 : Word)
          (srcPtr + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n - d))
          (1 : Word) (b.zeroExtend 64) (128 : Word)
          (BitVec.ofNat 64 (n - d)) h ?_
        xperm_hyp hp
    have hmid := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
        obtain ⟨h1, h2, hd12, hu, hBreak, hFr⟩ := hp
        obtain ⟨dd, hdd⟩ := hBreak
        obtain ⟨hcore, hpure⟩ := (sepConj_pure_right h1).1 hdd
        obtain ⟨rfl, _⟩ := hpure
        have hp' : (reubInvCore srcPtr (arenaPtr + BitVec.ofNat 64 off)
            raVal xs [] n d ** (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)) h :=
          ⟨h1, h2, hd12, hu, hcore, hFr⟩
        simp only [reubInvCore, reubStable, reubAmb, bytesRegion_nil,
          sepConj_emp_right', F] at hp'
        xperm_hyp hp') hbrk
      (cpsTripleWithin_of_forall_regIs_to_regOwn (fun w28 => htail w28))
    have hfull := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by unfold F at hp ⊢; xperm_hyp hp) hpro hmid
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hfull)
    · unfold reubAbiArenaPre at hp
      simp only [bytesRegion_nil, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp

  reub_spec_arena_header_aux (srcPtr arenaPtr raVal : Word)
      (v5 v6 v28 v29 v30 v31 : Word) (xs arenaBytes : List Byte)
      (off n : Nat) (hn : xs.length = n) (hn64 : n < 2 ^ 64)
      (hd : reubZeros xs 0 n < n)
      (hdom : n - reubZeros xs 0 n ≤ 55)
      (hhdr : ∀ b, reubStrip xs = [b] → 128 ≤ b.toNat)
      (hfit : off + n + 1 ≤ arenaBytes.length)
      (hsalign : srcPtr.toNat % 8 = 0) (hbase_align : arenaPtr.toNat % 8 = 0)
      (hsover : srcPtr.toNat + n < 2 ^ 64)
      (hover : arenaPtr.toNat + (off + n + 1) < 2 ^ 64)
      (hsvalid : ∀ k, k < n →
        isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
      (hvalid : ∀ k, k < n + 1 →
        isValidByteAccess (arenaPtr + BitVec.ofNat 64 (off + k)) = true) :
      cpsTripleWithin (n * 6 + 7 * (n - reubZeros xs 0 n) + 17)
        reubBase (raVal &&& ~~~1) reubCode
        (reubAbiArenaPre srcPtr arenaPtr raVal xs arenaBytes off n
          v5 v6 v28 v29 v30 v31)
        (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
    set d := reubZeros xs 0 n with hdef
    have hdlen : d < xs.length := by omega
    have hstrip : reubStrip xs = xs.drop d := reubStrip_eq_drop_zeros xs n hn
    have hLlen : (reubStrip xs).length = n - d :=
      reubStrip_length_eq xs n hn
    have hhdr' : ∀ b, reubStrip xs = [b] → ¬ b.toNat < 0x80 := by
      intro b hb
      have := hhdr b hb
      omega
    have hbyte : n - d = 1 → 128 ≤ (xs[d]'hdlen).toNat := by
      intro h1
      have hsingle : reubStrip xs = [xs[d]'hdlen] := by
        rw [hstrip]
        exact drop_eq_singleton xs d hdlen (by omega)
      have := hhdr' _ hsingle
      omega
    have hout : reubOut xs =
        BitVec.ofNat 8 (0x80 + (n - d)) :: xs.drop d := by
      have h := reubOut_header_form xs (by rw [hLlen]; omega)
        (by rw [hLlen]; omega) hhdr'
      rwa [hLlen, hstrip] at h
    have hlen : (reubOut xs).length = (n - d) + 1 := by
      rw [hout]
      simp [hn]
    have hregion :
        copyN (arenaBytes.set off (BitVec.ofNat 8 (128 + (n - d))))
            xs (off + 1) d (n - d) =
          setBytes arenaBytes off (reubOut xs) := by
      have hc := reub_header_copy_result arenaBytes xs off d n
        (BitVec.ofNat 8 (128 + (n - d))) hn (by omega) (by omega)
      rw [hc, hout]
    let F : Assertion :=
      ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
      ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion arenaPtr arenaBytes
    have hF : F.pcFree := by unfold F; pcFree
    have hpro := cpsTripleWithin_frameR F hF
      (reubPrologue srcPtr (arenaPtr + BitVec.ofNat 64 off) raVal
        v5 v6 v28 xs [] n)
    have hloop0 := reubStripLoop srcPtr (arenaPtr + BitVec.ofNat 64 off)
      raVal xs [] n (by omega) hn64 hsalign hsover hsvalid
    have hloop := cpsBranchWithin_frameR
      (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)
      (by unfold F; pcFree) hloop0
    have hbrk := cpsBranchWithin_takenPath hloop (fun _ hQf => by
      obtain ⟨_, _, _, _, hExh, _⟩ := hQf
      unfold reubExhPost at hExh
      have hpure := ((sepConj_pure_right _).1 hExh).2
      omega)
    have hrest : ∀ w29 w30, cpsTripleWithin (7 * (n - d) + 8)
        (reubBase + 84) (raVal &&& ~~~1) reubCode
        (reubHeaderPreArena srcPtr arenaPtr raVal xs arenaBytes n d off w29 w30 **
          ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n))
        (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
      intro w29 w30
      have hHW := reubHeaderWrite_arena srcPtr arenaPtr raVal xs arenaBytes n d off
        w29 w30 hbase_align (by omega) (by omega) (hvalid 0 (by omega))
      have hHWF := cpsTripleWithin_frameR
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) (by pcFree) hHW
      have hCL := reubCopyLoop srcPtr arenaPtr w30 xs
        (arenaBytes.set off (BitVec.ofNat 8 (128 + (n - d)))) d (off + 1)
        (n - d) hsalign hbase_align (by omega) (by rw [List.length_set]; omega)
        (by omega) (by omega) (by omega)
        (fun k hk => by
          have h := hsvalid (d + k) (by omega)
          simpa [Nat.add_assoc] using h)
        (fun k hk => by
          have h := hvalid (1 + k) (by omega)
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)
      have hCLF := cpsTripleWithin_frameR
        (((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (128 + (n - d))) **
         ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
         ((.x10 : Reg) ↦ᵣ srcPtr) **
         ((.x12 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 off)) **
         ((.x1 : Reg) ↦ᵣ raVal) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n))
        (by pcFree) hCL
      have hRT := reubRetTail raVal srcPtr (n - d)
      have hRTF := cpsTripleWithin_frameR
        (((.x6 : Reg) ↦ᵣ (0 : Word)) **
         ((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 (d + (n - d)))) **
         ((.x29 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 (off + 1 + (n - d)))) **
         regOwn .x30 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion srcPtr xs **
         bytesRegion arenaPtr
           (copyN (arenaBytes.set off (BitVec.ofNat 8 (128 + (n - d))))
             xs (off + 1) d (n - d)) **
         ((.x28 : Reg) ↦ᵣ BitVec.ofNat 64 (128 + (n - d))) **
         ((.x12 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 off)) **
         ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n)) (by pcFree) hRT
      have h12 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          simp only [reubCopyPreArena] at hp
          xperm_hyp hp) hHWF hCLF
      have h123 := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by xperm_hyp hp) h12 hRTF
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) h123)
      · simp only [reubHeaderPreArena] at hp ⊢
        xperm_hyp hp
      · unfold reubAbiArenaPost
        rw [← hregion, hlen, hn, word_ofNat_add_one]
        refine scratch_to_own_x30_arena srcPtr arenaPtr raVal xs
          (copyN (arenaBytes.set off (BitVec.ofNat 8 (128 + (n - d))))
            xs (off + 1) d (n - d)) off n
          (BitVec.ofNat 64 (n - d) + 1)
          (srcPtr + BitVec.ofNat 64 (d + (n - d))) (0 : Word)
          (BitVec.ofNat 64 (128 + (n - d)))
          (arenaPtr + BitVec.ofNat 64 (off + 1 + (n - d)))
          (BitVec.ofNat 64 (n - d)) h ?_
        xperm_hyp hp
    have htail : ∀ w28, cpsTripleWithin (7 * (n - d) + 14)
        (reubBase + 48) (raVal &&& ~~~1) reubCode
        ((((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
          bytesRegion srcPtr xs ** ((.x10 : Reg) ↦ᵣ srcPtr) **
          ((.x12 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 off)) **
          ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F) **
         ((.x28 : Reg) ↦ᵣ w28))
        (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
      intro w28
      by_cases h1 : n - d = 1
      · have hdisp := reubDispHeaderLarge srcPtr (arenaPtr + BitVec.ofNat 64 off)
          raVal xs [] n d w28 v29 v30 v31 hdlen h1 (hbyte h1) hsalign
          (by omega) (hsvalid d (by omega))
        have hdispF := cpsTripleWithin_frameR
          (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion arenaPtr arenaBytes)
          (by pcFree) hdisp
        have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          simp only [reubHeaderPreArena, reubHeaderPre, reubAmb,
            bytesRegion_nil, sepConj_emp_right'] at hp ⊢
          xperm_hyp hp)
          hdispF (hrest ((xs[d]'hdlen).zeroExtend 64) (128 : Word))
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hchain)
        simp only [reubDispPre, reubAmb,
          bytesRegion_nil, sepConj_emp_right', F] at hp ⊢
        xperm_hyp hp
      · have hdisp := reubDispHeaderLong srcPtr (arenaPtr + BitVec.ofNat 64 off)
          raVal xs [] n d w28 v29 v30 v31 h1 hn64
        have hdispF := cpsTripleWithin_frameR
          (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion arenaPtr arenaBytes)
          (by pcFree) hdisp
        have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
          simp only [reubHeaderPreArena, reubHeaderPre, reubAmb,
            bytesRegion_nil, sepConj_emp_right'] at hp ⊢
          xperm_hyp hp)
          hdispF (hrest v29 v30)
        refine cpsTripleWithin_mono_nSteps (by omega)
          (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hchain)
        simp only [reubDispPre, reubAmb,
          bytesRegion_nil, sepConj_emp_right', F] at hp ⊢
        xperm_hyp hp
    have hmid := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
        obtain ⟨h1, h2, hd12, hu, hBreak, hFr⟩ := hp
        obtain ⟨dd, hdd⟩ := hBreak
        obtain ⟨hcore, hpure⟩ := (sepConj_pure_right h1).1 hdd
        obtain ⟨rfl, _⟩ := hpure
        have hp' : (reubInvCore srcPtr (arenaPtr + BitVec.ofNat 64 off)
            raVal xs [] n d ** (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)) h :=
          ⟨h1, h2, hd12, hu, hcore, hFr⟩
        simp only [reubInvCore, reubStable, reubAmb, bytesRegion_nil,
          sepConj_emp_right', F] at hp'
        xperm_hyp hp') hbrk
      (cpsTripleWithin_of_forall_regIs_to_regOwn (fun w28 => htail w28))
    have hfull := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by unfold F at hp ⊢; xperm_hyp hp) hpro hmid
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hfull)
    · unfold reubAbiArenaPre at hp
      simp only [bytesRegion_nil, sepConj_emp_right'] at hp ⊢
      xperm_hyp hp

set_option maxRecDepth 8000 in
theorem reub_spec_arena_single_small (srcPtr arenaPtr raVal : Word)
    (v5 v6 v28 v29 v30 v31 : Word) (xs arenaBytes : List Byte)
    (off n : Nat) (hn : xs.length = n) (hn64 : n < 2 ^ 64)
    (hd : reubZeros xs 0 n < n)
    (hL : n - reubZeros xs 0 n = 1)
    (hdlen : reubZeros xs 0 n < xs.length)
    (hsmall : (xs[reubZeros xs 0 n]'hdlen).toNat < 128)
    (hfit : off + 1 ≤ arenaBytes.length)
    (hsalign : srcPtr.toNat % 8 = 0) (hbase_align : arenaPtr.toNat % 8 = 0)
    (hsover : srcPtr.toNat + n < 2 ^ 64)
    (hover : arenaPtr.toNat + off < 2 ^ 64)
    (hsvalid : ∀ k, k < n →
      isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ k, k < n + 1 →
      isValidByteAccess (arenaPtr + BitVec.ofNat 64 (off + k)) = true) :
    cpsTripleWithin (n * 6 + 12) reubBase (raVal &&& ~~~1) reubCode
      (reubAbiArenaPre srcPtr arenaPtr raVal xs arenaBytes off n
        v5 v6 v28 v29 v30 v31)
      (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
  set d := reubZeros xs 0 n with hdef
  set b := xs[d]'hdlen with hbdef
  have hstrip : reubStrip xs = [b] := by
    rw [reubStrip_eq_drop_zeros xs n hn, ← hdef]
    exact drop_eq_singleton xs d hdlen (by omega)
  have hout : reubOut xs = [b] :=
    reubOut_single_small xs b hstrip (by omega)
  have hlen1 : (reubOut xs).length = 1 := by rw [hout]; rfl
  let F : Assertion :=
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
    ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion arenaPtr arenaBytes
  have hF : F.pcFree := by unfold F; pcFree
  have hpro0 := reubPrologue srcPtr (arenaPtr + BitVec.ofNat 64 off)
    raVal v5 v6 v28 xs [] n
  have hpro := cpsTripleWithin_frameR F hF hpro0
  have hloop0 := reubStripLoop srcPtr (arenaPtr + BitVec.ofNat 64 off)
    raVal xs [] n (by omega) hn64 hsalign hsover hsvalid
  have hloop := cpsBranchWithin_frameR
    (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)
    (by unfold F; pcFree) hloop0
  have hbrk := cpsBranchWithin_takenPath hloop (fun _ hQf => by
    obtain ⟨_, _, _, _, hExh, _⟩ := hQf
    unfold reubExhPost at hExh
    have hpure := ((sepConj_pure_right _).1 hExh).2
    omega)
  have htail : ∀ w28, cpsTripleWithin 9 (reubBase + 48)
      (raVal &&& ~~~1) reubCode
      ((((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        ((.x31 : Reg) ↦ᵣ v31) ** bytesRegion srcPtr xs **
        ((.x10 : Reg) ↦ᵣ srcPtr) **
        ((.x12 : Reg) ↦ᵣ (arenaPtr + BitVec.ofNat 64 off)) **
        ((.x1 : Reg) ↦ᵣ raVal) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion arenaPtr arenaBytes) ** ((.x28 : Reg) ↦ᵣ w28))
      (reubAbiArenaPost srcPtr arenaPtr raVal xs arenaBytes off) := by
    intro w28
    have hdisp := reubDispSmallSingle srcPtr (arenaPtr + BitVec.ofNat 64 off)
      raVal xs [] n d w28 v29 v30 v31 hdlen hL hsmall hsalign (by omega)
      (hsvalid d (by omega))
    have hdispF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion arenaPtr arenaBytes)
      (by pcFree) hdisp
    have hsing := reubSingleTail_arena arenaPtr raVal srcPtr b
      arenaBytes off hbase_align (by omega) (by omega)
      (hvalid 0 (by omega))
    have hsingF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ (srcPtr + BitVec.ofNat 64 d)) **
       ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
       ((.x28 : Reg) ↦ᵣ (1 : Word)) ** ((.x30 : Reg) ↦ᵣ (128 : Word)) **
       ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (n - d)) **
       ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion srcPtr xs **
       ((.x0 : Reg) ↦ᵣ (0 : Word))) (by pcFree) hsing
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        simp only [reubSinglePre, reubAmb, bytesRegion_nil,
          sepConj_emp_right'] at hp
        xperm_hyp hp) hdispF hsingF
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hchain
    · simp only [reubDispPre, reubAmb, bytesRegion_nil,
        sepConj_emp_right'] at hp ⊢
      xperm_hyp hp
    · unfold reubAbiArenaPost
      rw [hlen1, hout, setBytes_singleton]
      simp only [hn]
      refine scratch_to_own_arena srcPtr arenaPtr raVal xs
        (arenaBytes.set off b) off n (1 : Word)
        (srcPtr + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n - d))
        (1 : Word) (b.zeroExtend 64) (128 : Word)
        (BitVec.ofNat 64 (n - d)) h ?_
      xperm_hyp hp
  have hmid := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      obtain ⟨h1, h2, hd12, hu, hBreak, hFr⟩ := hp
      obtain ⟨dd, hdd⟩ := hBreak
      obtain ⟨hcore, hpure⟩ := (sepConj_pure_right h1).1 hdd
      obtain ⟨rfl, _⟩ := hpure
      have hp' : (reubInvCore srcPtr (arenaPtr + BitVec.ofNat 64 off)
          raVal xs [] n d ** (((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** F)) h :=
        ⟨h1, h2, hd12, hu, hcore, hFr⟩
      simp only [reubInvCore, reubStable, reubAmb, bytesRegion_nil,
        sepConj_emp_right', F] at hp'
      xperm_hyp hp') hbrk
    (cpsTripleWithin_of_forall_regIs_to_regOwn (fun w28 => htail w28))
  have hfull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by unfold F at hp ⊢; xperm_hyp hp) hpro hmid
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hp => hp) hfull)
  · unfold reubAbiArenaPre at hp
    simp only [bytesRegion_nil, sepConj_emp_right'] at hp ⊢
    xperm_hyp hp

end RlpEncodeUintBeSAsm
end EvmAsm.Codegen
