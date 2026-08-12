/-
  EvmAsm.Codegen.Programs.NodeDbLookupSpec

  **Whole-routine machine triple for the guest routine `node_db_lookup`**
  (GH #11800, the node-DB half).

  `node_db_lookup` (`EvmAsm/Codegen/Programs/MptSetAcc.lean:139`,
  33 instructions) is the reader of the appended node DB that
  `node_db_append` builds: a linear scan over `mset_db_count` records
  starting at `mset_db_data`, comparing the 32-byte keccak stored in each
  record's first four dwords against the caller's target hash, and — on the
  first match — writing the ABSOLUTE address of the record's node bytes to
  `*a1`, the node length to `*a2`, and returning `a0 = 0`; `a0 = 1` on
  exhaustion.

  ## What is proved here

  `node_db_lookup_spec_within` is a `cpsTripleWithin` over
  `CodeReq.ofProg (GuestAddrs.node_db_lookup) nodeDbLookup_prog` — the
  linked program itself, not a model of it — from the routine's linked
  entry to the caller's return address. Its post is a `match` on the
  machine-level find function `nodeDbFind`, so the two arms are pinned
  ASYMMETRICALLY: the hit arm names the out-pointer cell and the out-length
  cell separately (swapping them would not typecheck against the record
  layout), and the miss arm says both cells are *untouched*, not merely
  owned.

  ## Why this composes to the spec reference

  `nodeDbFind` is the address-carrying refinement of `nodeDbLookupSpec`
  (`EvmAsm/Evm64/MptAssertions.lean:791`), and
  `nodeDbFind_eq_lookupSpec` below identifies the two. `MptAssertions`
  already proves `nodeDbLookupSpec_eq_build_node_db`, so
  `nodeDbFind_eq_build_node_db` carries the machine post all the way to
  `Stateless.SpecRef.build_node_db` — the port of `witness_state.py`'s
  `Dict[keccak256(entry), entry]`. The model↔reference leg was already
  closed; this module supplies the machine↔model leg.

  ## The keccak leg

  `node_db_lookup` never hashes: it compares the hash STORED in the record
  (which `node_db_append` computed via `zkvm_keccak256`) against the
  caller's target bytes. So no keccak obligation arises here at all — the
  triple's hypotheses mention `Stateless.SpecRef.keccak256` only through
  `nodeDbRecordBytes`, and the only fact needed about it is that a digest
  is 32 bytes long (`hkLen`), which is a layout fact about the record, not
  a fact about the hash function. Nothing is hypothesised about keccak's
  VALUE.
-/

import EvmAsm.Rv64.SAsm.TwoBreakWritable
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.SAsm.StmtSound
import EvmAsm.Rv64.LaResolve
import EvmAsm.Evm64.MptAssertions
import EvmAsm.Codegen.Programs.MptSetAcc

namespace EvmAsm.Codegen.NodeDbLookupSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Evm64

/-! ## §1  The address-carrying model

    `nodeDbLookupSpec` (MptAssertions) answers *which node*; the machine
    answers *where it is*. `nodeDbFind` is the same scan carrying the
    record cursor, so the triple's post can name the exact word the routine
    stores. -/

/-- The scan `node_db_lookup` performs, carrying the cursor: walking the
    record log from `base`, the first record whose stored 32-byte keccak
    equals `h` yields the ABSOLUTE address of its node bytes
    (`cursor + 40`, past the 32-byte hash and the 8-byte length) and that
    node's length. -/
def nodeDbFind (base : Word) (nodes : List (List (BitVec 8)))
    (h : List (BitVec 8)) : Option (Word × Nat) :=
  match nodes with
  | [] => none
  | n :: rest =>
      if Stateless.SpecRef.keccak256 n = h then some (base + (40 : Word), n.length)
      else nodeDbFind (base + BitVec.ofNat 64 (nodeDbStride n)) rest h

@[simp] theorem nodeDbFind_nil (base : Word) (h : List (BitVec 8)) :
    nodeDbFind base [] h = none := rfl

theorem nodeDbFind_cons (base : Word) (n : List (BitVec 8))
    (rest : List (List (BitVec 8))) (h : List (BitVec 8)) :
    nodeDbFind base (n :: rest) h =
      if Stateless.SpecRef.keccak256 n = h then some (base + (40 : Word), n.length)
      else nodeDbFind (base + BitVec.ofNat 64 (nodeDbStride n)) rest h := rfl

/-- **The machine model refines the `MptAssertions` model.** The cursor is
    extra information: forgetting it recovers `nodeDbLookupSpec` exactly, so
    the found record's length is the found node's length and a miss is a
    miss. -/
theorem nodeDbFind_eq_lookupSpec (base : Word) (nodes : List (List (BitVec 8)))
    (h : List (BitVec 8)) :
    (nodeDbFind base nodes h).map Prod.snd =
      (nodeDbLookupSpec nodes h).map List.length := by
  induction nodes generalizing base with
  | nil => rfl
  | cons n rest ih =>
    rw [nodeDbFind_cons]
    show _ = ((n :: rest).find? _).map _
    rw [List.find?_cons]
    by_cases hk : Stateless.SpecRef.keccak256 n = h
    · rw [if_pos hk, show (Stateless.SpecRef.keccak256 n == h) = true from by simp [hk]]
      rfl
    · rw [if_neg hk, show (Stateless.SpecRef.keccak256 n == h) = false from by simp [hk]]
      exact ih _

/-- A miss for the machine model is a miss for `nodeDbLookupSpec`. -/
theorem nodeDbFind_none_iff (base : Word) (nodes : List (List (BitVec 8)))
    (h : List (BitVec 8)) :
    nodeDbFind base nodes h = none ↔ nodeDbLookupSpec nodes h = none := by
  constructor
  · intro hf
    have := nodeDbFind_eq_lookupSpec base nodes h
    rw [hf] at this
    exact Option.map_eq_none_iff.mp this.symm
  · intro hf
    have := nodeDbFind_eq_lookupSpec base nodes h
    rw [hf] at this
    exact Option.map_eq_none_iff.mp this

/-- **Composition to the spec reference.** `nodeDbLookupSpec_eq_build_node_db`
    (`MptAssertions.lean:806`) already ties the scan model to
    `Stateless.SpecRef.build_node_db` — the Lean port of `witness_state.py`'s
    `Dict[keccak256(entry), entry]`. Chaining it through
    `nodeDbFind_eq_lookupSpec` carries the MACHINE post to the reference. -/
theorem nodeDbFind_eq_build_node_db (base : Word) (nodes : List (List (BitVec 8)))
    (h : List (BitVec 8)) :
    (nodeDbFind base nodes h).map Prod.snd =
      ((Stateless.SpecRef.build_node_db nodes).lookup h).map List.length := by
  rw [nodeDbFind_eq_lookupSpec, nodeDbLookupSpec_eq_build_node_db]

/-! ## §2  Byte/dword bridges

    The routine compares 32-byte digests four dwords at a time. These
    lemmas are the only place the byte-list model and the machine's
    `packBytes` view meet. -/

/-- Dword `q` of a byte list, as the machine reads it. -/
abbrev dwordOf (bs : List (BitVec 8)) (q : Nat) : Word :=
  packBytes ((bs.drop (8 * q)).take 8)

/-- **Four dwords decide a 32-byte comparison.** Equal digests obviously
    have equal dwords; conversely four equal dwords force all 32 bytes,
    so the routine's four-`BNE` cascade is exactly a digest comparison —
    it cannot accept a different 32-byte string. -/
theorem eq_of_dwords_eq {a b : List (BitVec 8)}
    (ha : a.length = 32) (hb : b.length = 32)
    (hq : ∀ q, q < 4 → dwordOf a q = dwordOf b q) : a = b := by
  apply List.ext_getElem (by rw [ha, hb])
  intro k hka hkb
  have hk32 : k < 32 := by omega
  have hchunk : ∀ (c : List (BitVec 8)) (hc : c.length = 32),
      extractByte (dwordOf c (k / 8)) (k % 8) = c[k]'(by omega) := by
    intro c hc
    have hlt8 : k % 8 < 8 := Nat.mod_lt _ (by omega)
    have hlen : k % 8 < ((c.drop (8 * (k / 8))).take 8).length := by
      rw [List.length_take, List.length_drop, hc]
      omega
    rw [dwordOf, extractByte_packBytes _ _ hlt8 hlen]
    have : ((c.drop (8 * (k / 8))).take 8)[k % 8]'hlen = c[8 * (k / 8) + k % 8]'(by omega) := by
      rw [List.getElem_take, List.getElem_drop]
    rw [this]
    congr 1
    omega
  have h1 := hchunk a ha
  have h2 := hchunk b hb
  rw [← h1, ← h2, hq (k / 8) (by omega)]

/-- The contrapositive the mismatch arm uses: one differing dword is enough
    to conclude the digests differ. -/
theorem ne_of_dword_ne {a b : List (BitVec 8)} {q : Nat}
    (hq : dwordOf a q ≠ dwordOf b q) : a ≠ b := by
  intro hab; exact hq (by rw [hab])

/-- A dword read of an appended prefix is a dword read of the prefix, as
    long as the dword lies inside it. -/
theorem dwordOf_append_left (a b : List (BitVec 8)) (q : Nat)
    (hq : 8 * q + 8 ≤ a.length) : dwordOf (a ++ b) q = dwordOf a q := by
  have hle : 8 * q ≤ a.length := by omega
  rw [dwordOf, dwordOf, List.drop_append_of_le_length hle,
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

private theorem extractByte_ofNat (m j : Nat) (hm : m < 2 ^ 64) :
    extractByte (BitVec.ofNat 64 m) j = BitVec.ofNat 8 (m >>> (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  rw [show j * 8 = 8 * j from by omega]

/-- The stored little-endian length dword reads back as the length. -/
theorem packBytes_natToBytesLE8 (m : Nat) (hm : m < 2 ^ 64) :
    packBytes (Stateless.SpecRef.natToBytesLE 8 m) = BitVec.ofNat 64 m := by
  have hbytes : Stateless.SpecRef.natToBytesLE 8 m = dwordBytes (BitVec.ofNat 64 m) := by
    show (List.range 8).map _ = _
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    show [_, _, _, _, _, _, _, _] = _
    rw [dwordBytes, extractByte_ofNat m 0 hm, extractByte_ofNat m 1 hm,
      extractByte_ofNat m 2 hm, extractByte_ofNat m 3 hm, extractByte_ofNat m 4 hm,
      extractByte_ofNat m 5 hm, extractByte_ofNat m 6 hm, extractByte_ofNat m 7 hm]
  rw [hbytes, packBytes_dwordBytes]

/-! ## §3  Record layout: what the four hash dwords and the length dword are -/

/-- The record, re-associated so the digest is the visible prefix. -/
theorem nodeDbRecordBytes_eq (n : List (BitVec 8)) :
    nodeDbRecordBytes n =
      Stateless.SpecRef.keccak256 n ++
        (Stateless.SpecRef.natToBytesLE 8 n.length ++
          (n ++ List.replicate (roundUp8 n.length - n.length) 0)) := by
  rw [nodeDbRecordBytes, List.append_assoc, List.append_assoc]

/-- Dwords 0..3 of a record are exactly the four dwords of the digest
    `node_db_append` stored — so the routine's four-`BNE` cascade compares
    digests, nothing else. -/
theorem dwordOf_record_hash (n : List (BitVec 8)) (q : Nat) (hq : q < 4)
    (hk : (Stateless.SpecRef.keccak256 n).length = 32) :
    dwordOf (nodeDbRecordBytes n) q = dwordOf (Stateless.SpecRef.keccak256 n) q := by
  rw [nodeDbRecordBytes_eq]
  exact dwordOf_append_left _ _ q (by rw [hk]; omega)

/-- Dword 4 of a record is the stored node length. -/
theorem dwordOf_record_len (n : List (BitVec 8))
    (hk : (Stateless.SpecRef.keccak256 n).length = 32)
    (hn : n.length < 2 ^ 64) :
    dwordOf (nodeDbRecordBytes n) 4 = BitVec.ofNat 64 n.length := by
  have hdrop : (nodeDbRecordBytes n).drop (8 * 4) =
      Stateless.SpecRef.natToBytesLE 8 n.length ++
        (n ++ List.replicate (roundUp8 n.length - n.length) 0) := by
    rw [nodeDbRecordBytes_eq,
      List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  rw [dwordOf, hdrop,
    List.take_append_of_le_length (by simp),
    List.take_of_length_le (by simp),
    packBytes_natToBytesLE8 _ hn]

/-- A record is at least 40 bytes: the digest, then the length dword. -/
theorem record_length_ge40 (n : List (BitVec 8))
    (hk : (Stateless.SpecRef.keccak256 n).length = 32) :
    40 ≤ (nodeDbRecordBytes n).length := by
  rw [nodeDbRecordBytes_length n hk, nodeDbStride]
  omega

/-! ## §4  Scan arithmetic: prefix sizes and first-match identification -/

theorem nodeDbSize_snoc (xs : List (List (BitVec 8))) (n : List (BitVec 8)) :
    nodeDbSize (xs ++ [n]) = nodeDbSize xs + nodeDbStride n := by
  induction xs with
  | nil => simp [nodeDbSize]
  | cons a rest ih =>
    rw [List.cons_append, nodeDbSize_cons, ih, nodeDbSize_cons]
    omega

/-- Scanning past a non-matching record keeps the "no hit yet" invariant. -/
theorem lookupSpec_none_snoc (xs : List (List (BitVec 8))) (n : List (BitVec 8))
    (h : List (BitVec 8)) (hxs : nodeDbLookupSpec xs h = none)
    (hne : Stateless.SpecRef.keccak256 n ≠ h) :
    nodeDbLookupSpec (xs ++ [n]) h = none := by
  show (xs ++ [n]).find? _ = none
  rw [List.find?_append, show xs.find? _ = none from hxs, Option.none_or,
    List.find?_cons, show (Stateless.SpecRef.keccak256 n == h) = false from by simp [hne]]
  rfl

/-- **The first match is the answer.** With no hit in the first `j` records
    and a hit at record `j`, the machine model resolves to the address the
    routine computes (`cursor + 40`) and that record's node length. -/
theorem nodeDbFind_at (base : Word) (nodes : List (List (BitVec 8)))
    (h : List (BitVec 8)) (j : Nat) (hj : j < nodes.length)
    (hnone : nodeDbLookupSpec (nodes.take j) h = none)
    (hmatch : Stateless.SpecRef.keccak256 nodes[j] = h) :
    nodeDbFind base nodes h =
      some (base + BitVec.ofNat 64 (nodeDbSize (nodes.take j)) + (40 : Word),
        nodes[j].length) := by
  induction j generalizing base nodes with
  | zero =>
    obtain ⟨n, rest, rfl⟩ : ∃ n rest, nodes = n :: rest := by
      cases nodes with
      | nil => simp at hj
      | cons a r => exact ⟨a, r, rfl⟩
    rw [nodeDbFind_cons, if_pos (by simpa using hmatch)]
    simp [nodeDbSize]
  | succ k ih =>
    obtain ⟨n, rest, rfl⟩ : ∃ n rest, nodes = n :: rest := by
      cases nodes with
      | nil => simp at hj
      | cons a r => exact ⟨a, r, rfl⟩
    rw [List.take_succ_cons] at hnone
    have hfind : ((n :: rest.take k).find?
        (fun m => Stateless.SpecRef.keccak256 m == h)) = none := hnone
    have hk0 : Stateless.SpecRef.keccak256 n ≠ h := by
      intro hc
      rw [List.find?_cons_of_pos (by simp [hc])] at hfind
      exact absurd hfind (by simp)
    have hnone' : nodeDbLookupSpec (rest.take k) h = none := by
      rw [List.find?_cons_of_neg (by simp [hk0])] at hfind
      exact hfind
    rw [nodeDbFind_cons, if_neg hk0]
    have hstep := ih (base + BitVec.ofNat 64 (nodeDbStride n)) rest
      (by simpa using hj) hnone' (by simpa using hmatch)
    rw [hstep]
    congr 2
    rw [List.take_succ_cons, nodeDbSize_cons, add_ofNat_add_ofNat]

/-- `take (j+1)` as `take j` with the `j`-th record appended — the shape both
    the prefix size and the "no hit yet" invariant advance through. -/
theorem take_succ_snoc (nodes : List (List (BitVec 8))) (j : Nat) (hj : j < nodes.length) :
    nodes.take (j + 1) = nodes.take j ++ [nodes[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  rfl

/-! ## §5  Memory: splitting the record log at the cursor -/

/-- The record log, split at the cursor the loop holds: the records already
    scanned, the record under the cursor, and the records still to come. -/
theorem nodeDbIs_split_at (base : Word) (nodes : List (List (BitVec 8))) (j : Nat)
    (hj : j < nodes.length) :
    nodeDbIs base nodes =
      (nodeDbIs base (nodes.take j) **
        (bytesRegion (base + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
            (nodeDbRecordBytes nodes[j]) **
          nodeDbIs (base + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
            (nodes.drop (j + 1)))) := by
  conv_lhs => rw [show nodes = nodes.take j ++ nodes.drop j from
    (List.take_append_drop j nodes).symm]
  rw [nodeDbIs_append, List.drop_eq_getElem_cons hj, nodeDbIs_cons,
    take_succ_snoc nodes j hj, nodeDbSize_snoc, add_ofNat_add_ofNat]


/-! ## §6  The linked routine

    Every triple below is stated over `ndlCr` — the emitted program
    `nodeDbLookup_prog` at its linked guest address — so the machine is
    named in each of them. -/

/-- The routine's linked entry (`GuestAddrs.node_db_lookup`). -/
def ndlB : Word := (GuestAddrs.node_db_lookup : Word)

/-- The routine's own code requirement: the 33-instruction emitted program
    at its linked address. -/
def ndlCr : CodeReq := CodeReq.ofProg ndlB nodeDbLookup_prog

/-- `mset_db_data` — the record log's base. -/
def dbBase : Word := (GuestAddrs.mset_db_data : Word)

/-- `mset_db_count` — the record-count cell. -/
def cntLoc : Word := (GuestAddrs.mset_db_count : Word)

/-! ### The hit tail (`idx 18..23`)

    `addi x5, x30, 40 ; sd x5, 0(x11) ; ld x6, 32(x30) ; sd x6, 0(x12) ;
     li a0, 0 ; ret` — the out-pointer cell gets the record's NODE-BYTES
    address and the out-length cell gets the record's length; the two are
    written from different registers to different cells, so the post is not
    symmetric in them. -/
private theorem hitTail_spec (retAddr cur outP outL a0old v5 v6 o1 o2 : Word)
    (recBytes : List (BitVec 8)) (len : Nat)
    (hlen40 : 40 ≤ recBytes.length)
    (hd4 : dwordOf recBytes 4 = BitVec.ofNat 64 len)
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr) :
    cpsTripleWithin 6 (ndlB + 72) retAddr ndlCr
      (((.x30 : Reg) ↦ᵣ cur) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
        (outP ↦ₘ o1) ** (outL ↦ₘ o2) ** bytesRegion cur recBytes **
        ((.x10 : Reg) ↦ᵣ a0old) ** ((.x1 : Reg) ↦ᵣ retAddr))
      (((.x30 : Reg) ↦ᵣ cur) ** ((.x5 : Reg) ↦ᵣ (cur + (40 : Word))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 len) **
        ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
        (outP ↦ₘ (cur + (40 : Word))) ** (outL ↦ₘ BitVec.ofNat 64 len) **
        bytesRegion cur recBytes **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr)) := by
  -- idx 18: addi x5, x30, 40
  have h18 := liftCode (cr' := ndlCr)
    (addi_spec_gen_within .x5 .x30 v5 cur (40 : BitVec 12) (ndlB + 72) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide,
    show (ndlB + 72 : Word) + 4 = ndlB + 76 from by bv_omega] at h18
  -- idx 19: sd x5, 0(x11)
  have h19 := liftCode (cr' := ndlCr)
    (sd_spec_gen_within .x11 .x5 outP (cur + (40 : Word)) o1 (0 : BitVec 12) (ndlB + 76))
    (by unfold ndlCr; code_mem)
  rw [show outP + signExtend12 (0 : BitVec 12) = outP from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (ndlB + 76 : Word) + 4 = ndlB + 80 from by bv_omega] at h19
  -- idx 20: ld x6, 32(x30)
  have h20 := liftCode (cr' := ndlCr)
    (bytesRegion_ld_within .x6 .x30 cur v6 (ndlB + 80) recBytes 4 (by decide)
      (by omega) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show packBytes ((recBytes.drop (8 * 4)).take 8) = BitVec.ofNat 64 len from hd4,
    show (ndlB + 80 : Word) + 4 = ndlB + 84 from by bv_omega] at h20
  -- idx 21: sd x6, 0(x12)
  have h21 := liftCode (cr' := ndlCr)
    (sd_spec_gen_within .x12 .x6 outL (BitVec.ofNat 64 len) o2 (0 : BitVec 12) (ndlB + 84))
    (by unfold ndlCr; code_mem)
  rw [show outL + signExtend12 (0 : BitVec 12) = outL from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (ndlB + 84 : Word) + 4 = ndlB + 88 from by bv_omega] at h21
  -- idx 22: li a0, 0
  have h22 := liftCode (cr' := ndlCr)
    (li_spec_gen_within .x10 a0old (0 : Word) (ndlB + 88) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show (ndlB + 88 : Word) + 4 = ndlB + 92 from by bv_omega] at h22
  -- idx 23: ret
  have h23 := liftCode (cr' := ndlCr)
    (EvmAsm.Evm64.ret_spec_within' (ndlB + 92) retAddr)
    (by unfold ndlCr; code_mem)
  rw [halign] at h23
  -- frame each step with the conjuncts it does not touch
  have f18 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
      (outP ↦ₘ o1) ** (outL ↦ₘ o2) ** bytesRegion cur recBytes **
      ((.x10 : Reg) ↦ᵣ a0old) ** ((.x1 : Reg) ↦ᵣ retAddr)) (by pcf) h18
  have f19 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x12 : Reg) ↦ᵣ outL) **
      (outL ↦ₘ o2) ** bytesRegion cur recBytes **
      ((.x10 : Reg) ↦ᵣ a0old) ** ((.x1 : Reg) ↦ᵣ retAddr)) (by pcf) h19
  have f20 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ (cur + (40 : Word))) ** ((.x11 : Reg) ↦ᵣ outP) **
      ((.x12 : Reg) ↦ᵣ outL) ** (outP ↦ₘ (cur + (40 : Word))) ** (outL ↦ₘ o2) **
      ((.x10 : Reg) ↦ᵣ a0old) ** ((.x1 : Reg) ↦ᵣ retAddr)) (by pcf) h20
  have f21 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x5 : Reg) ↦ᵣ (cur + (40 : Word))) **
      ((.x11 : Reg) ↦ᵣ outP) ** (outP ↦ₘ (cur + (40 : Word))) **
      bytesRegion cur recBytes ** ((.x10 : Reg) ↦ᵣ a0old) **
      ((.x1 : Reg) ↦ᵣ retAddr)) (by pcf) h21
  have f22 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x5 : Reg) ↦ᵣ (cur + (40 : Word))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x11 : Reg) ↦ᵣ outP) **
      ((.x12 : Reg) ↦ᵣ outL) ** (outP ↦ₘ (cur + (40 : Word))) **
      (outL ↦ₘ BitVec.ofNat 64 len) ** bytesRegion cur recBytes **
      ((.x1 : Reg) ↦ᵣ retAddr)) (by pcf) h22
  have f23 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x5 : Reg) ↦ᵣ (cur + (40 : Word))) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 len) ** ((.x11 : Reg) ↦ᵣ outP) **
      ((.x12 : Reg) ↦ᵣ outL) ** (outP ↦ₘ (cur + (40 : Word))) **
      (outL ↦ₘ BitVec.ofNat 64 len) ** bytesRegion cur recBytes **
      ((.x10 : Reg) ↦ᵣ (0 : Word))) (by pcf) h23
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f18 f19
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f20
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f21
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f22
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 f23
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c5


/-! ### The advance tail (`idx 24..30`)

    `ld x6, 32(x30) ; addi x6, x6, 7 ; andi x6, x6, -8 ; addi x6, x6, 40 ;
     add x30, x30, x6 ; addi x31, x31, -1 ; jal hdr` — the cursor bumps by
    EXACTLY `nodeDbStride`, the record size `node_db_append` reserved. The
    `andi -8` is `roundUp8` (`roundUp8_eq_alignToDword`, MptAssertions). -/
private theorem advanceTail_spec (cur cnt v6 : Word) (recBytes : List (BitVec 8))
    (len stride : Nat)
    (hlen40 : 40 ≤ recBytes.length)
    (hd4 : dwordOf recBytes 4 = BitVec.ofNat 64 len)
    (hlen : len + 7 < 2 ^ 64)
    (hstride : stride = 40 + roundUp8 len) :
    cpsTripleWithin 7 (ndlB + 96) (ndlB + 20) ndlCr
      (((.x30 : Reg) ↦ᵣ cur) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x31 : Reg) ↦ᵣ cnt) **
        bytesRegion cur recBytes)
      (((.x30 : Reg) ↦ᵣ (cur + BitVec.ofNat 64 stride)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 stride) **
        ((.x31 : Reg) ↦ᵣ (cnt - 1)) ** bytesRegion cur recBytes) := by
  have hadd7 : BitVec.ofNat 64 len + signExtend12 (7 : BitVec 12)
      = BitVec.ofNat 64 (len + 7) := by
    rw [show signExtend12 (7 : BitVec 12) = (7 : Word) from by decide]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      show (7 : Word).toNat = 7 from by decide]
    omega
  have hand : BitVec.ofNat 64 (len + 7) &&& signExtend12 (-8 : BitVec 12)
      = BitVec.ofNat 64 (roundUp8 len) := by
    rw [roundUp8_eq_alignToDword len hlen, alignToDword,
      show signExtend12 (-8 : BitVec 12) = ~~~7#64 from by decide]
  have hadd40 : BitVec.ofNat 64 (roundUp8 len) + signExtend12 (40 : BitVec 12)
      = BitVec.ofNat 64 stride := by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide, hstride]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      show (40 : Word).toNat = 40 from by decide]
    omega
  -- idx 24: ld x6, 32(x30)
  have h24 := liftCode (cr' := ndlCr)
    (bytesRegion_ld_within .x6 .x30 cur v6 (ndlB + 96) recBytes 4 (by decide)
      (by omega) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show packBytes ((recBytes.drop (8 * 4)).take 8) = BitVec.ofNat 64 len from hd4,
    show (ndlB + 96 : Word) + 4 = ndlB + 100 from by bv_omega] at h24
  -- idx 25: addi x6, x6, 7
  have h25 := liftCode (cr' := ndlCr)
    (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 len) (7 : BitVec 12)
      (ndlB + 100) (by decide))
    (by unfold ndlCr; code_mem)
  rw [hadd7, show (ndlB + 100 : Word) + 4 = ndlB + 104 from by bv_omega] at h25
  -- idx 26: andi x6, x6, -8
  have h26 := liftCode (cr' := ndlCr)
    (andi_spec_gen_same_within .x6 (BitVec.ofNat 64 (len + 7)) (-8 : BitVec 12)
      (ndlB + 104) (by decide))
    (by unfold ndlCr; code_mem)
  rw [hand, show (ndlB + 104 : Word) + 4 = ndlB + 108 from by bv_omega] at h26
  -- idx 27: addi x6, x6, 40
  have h27 := liftCode (cr' := ndlCr)
    (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (roundUp8 len)) (40 : BitVec 12)
      (ndlB + 108) (by decide))
    (by unfold ndlCr; code_mem)
  rw [hadd40, show (ndlB + 108 : Word) + 4 = ndlB + 112 from by bv_omega] at h27
  -- idx 28: add x30, x30, x6
  have h28 := liftCode (cr' := ndlCr)
    (add_spec_gen_rd_eq_rs1_within .x30 .x6 cur (BitVec.ofNat 64 stride)
      (ndlB + 112) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show (ndlB + 112 : Word) + 4 = ndlB + 116 from by bv_omega] at h28
  -- idx 29: addi x31, x31, -1
  have h29 := liftCode (cr' := ndlCr)
    (addi_spec_gen_same_within .x31 cnt (-1 : BitVec 12) (ndlB + 116) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show cnt + signExtend12 (-1 : BitVec 12) = cnt - 1 from by
      rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]; bv_omega,
    show (ndlB + 116 : Word) + 4 = ndlB + 120 from by bv_omega] at h29
  -- idx 30: jal x0, hdr
  have h30 := liftCode (cr' := ndlCr)
    (jal_x0_spec_gen_within (-100 : BitVec 21) (ndlB + 120))
    (by unfold ndlCr; code_mem)
  rw [show (ndlB + 120 : Word) + signExtend21 (-100 : BitVec 21) = ndlB + 20 from by
      rw [show signExtend21 (-100 : BitVec 21) = (-100 : Word) from by decide]; bv_omega]
    at h30
  have f24 := cpsTripleWithin_frameR (((.x31 : Reg) ↦ᵣ cnt)) (by pcf) h24
  have f25 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x31 : Reg) ↦ᵣ cnt) ** bytesRegion cur recBytes)
    (by pcf) h25
  have f26 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x31 : Reg) ↦ᵣ cnt) ** bytesRegion cur recBytes)
    (by pcf) h26
  have f27 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x31 : Reg) ↦ᵣ cnt) ** bytesRegion cur recBytes)
    (by pcf) h27
  have f28 := cpsTripleWithin_frameR
    (((.x31 : Reg) ↦ᵣ cnt) ** bytesRegion cur recBytes) (by pcf) h28
  have f29 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ (cur + BitVec.ofNat 64 stride)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 stride) ** bytesRegion cur recBytes)
    (by pcf) h29
  have f30 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ (cur + BitVec.ofNat 64 stride)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 stride) ** ((.x31 : Reg) ↦ᵣ (cnt - 1)) **
      bytesRegion cur recBytes) (by pcf) h30
  rw [sepConj_emp_left'] at f30
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f24 f25
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f26
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 f27
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 f28
  have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c4 f29
  have c6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c5 f30
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c6


/-! ### One compare station (`ld x5, 8q(x30) ; ld x6, 8q(x10) ; bne x5, x6`)

    Dword `q` of the record under the cursor is compared against dword `q`
    of the caller's target hash. The mismatch arm and the match arm are
    handed the DECIDED fact, so each continuation is entered only on its own
    inputs. -/
private theorem station_step
    (q : Nat) (addr : Word) (boff : BitVec 13)
    (cur hashPtr v5 v6 retAddr : Word) (recBytes hsh : List (BitVec 8))
    (FR Q I : Assertion) (hFR : FR.pcFree) (K : Nat)
    (hrec : 8 * q < recBytes.length) (hhsh : 8 * q < hsh.length)
    (himm : 8 * q < 2 ^ 11)
    (hm1 : ∀ a i, CodeReq.singleton addr
      (.LD .x5 .x30 (BitVec.ofNat 12 (8 * q))) a = some i → ndlCr a = some i)
    (hm2 : ∀ a i, CodeReq.singleton (addr + 4)
      (.LD .x6 .x10 (BitVec.ofNat 12 (8 * q))) a = some i → ndlCr a = some i)
    (hm3 : ∀ a i, CodeReq.singleton (addr + 8)
      (.BNE .x5 .x6 boff) a = some i → ndlCr a = some i)
    (hmis : dwordOf recBytes q ≠ dwordOf hsh q →
      cpsBranchWithin K (addr + 8 + signExtend13 boff) ndlCr
        (((.x5 : Reg) ↦ᵣ dwordOf recBytes q) ** ((.x6 : Reg) ↦ᵣ dwordOf hsh q) **
          ((.x30 : Reg) ↦ᵣ cur) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
          bytesRegion cur recBytes ** bytesRegion hashPtr hsh ** FR)
        retAddr Q (ndlB + 20) I)
    (hhit : dwordOf recBytes q = dwordOf hsh q →
      cpsBranchWithin K (addr + 12) ndlCr
        (((.x5 : Reg) ↦ᵣ dwordOf recBytes q) ** ((.x6 : Reg) ↦ᵣ dwordOf hsh q) **
          ((.x30 : Reg) ↦ᵣ cur) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
          bytesRegion cur recBytes ** bytesRegion hashPtr hsh ** FR)
        retAddr Q (ndlB + 20) I) :
    cpsBranchWithin (2 + (1 + K)) addr ndlCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x30 : Reg) ↦ᵣ cur) **
        ((.x10 : Reg) ↦ᵣ hashPtr) ** bytesRegion cur recBytes **
        bytesRegion hashPtr hsh ** FR)
      retAddr Q (ndlB + 20) I := by
  have hA := liftCode (cr' := ndlCr)
    (bytesRegion_ld_within .x5 .x30 cur v5 addr recBytes q (by decide) hrec himm) hm1
  have hB := liftCode (cr' := ndlCr)
    (bytesRegion_ld_within .x6 .x10 hashPtr v6 (addr + 4) hsh q (by decide) hhsh himm) hm2
  rw [show (addr + 4 : Word) + 4 = addr + 8 from by bv_omega] at hB
  have hC := cpsBranchWithin_extend_code hm3
    (bne_spec_gen_within .x5 .x6 boff (dwordOf recBytes q) (dwordOf hsh q) (addr + 8))
  rw [show (addr + 8 : Word) + 4 = addr + 12 from by bv_omega] at hC
  have fA := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
      bytesRegion hashPtr hsh ** FR) (by pcf; exact hFR) hA
  have fB := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ dwordOf recBytes q) ** ((.x30 : Reg) ↦ᵣ cur) **
      bytesRegion cur recBytes ** FR) (by pcf; exact hFR) hB
  have fC := cpsBranchWithin_frameR
    (((.x30 : Reg) ↦ᵣ cur) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
      bytesRegion cur recBytes ** bytesRegion hashPtr hsh ** FR) (by pcf; exact hFR) hC
  have hT := cpsBranchWithin_weaken
    (P := ⌜dwordOf recBytes q ≠ dwordOf hsh q⌝ **
      (((.x5 : Reg) ↦ᵣ dwordOf recBytes q) ** ((.x6 : Reg) ↦ᵣ dwordOf hsh q) **
        ((.x30 : Reg) ↦ᵣ cur) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
        bytesRegion cur recBytes ** bytesRegion hashPtr hsh ** FR))
    (P' := ((((.x5 : Reg) ↦ᵣ dwordOf recBytes q) ** ((.x6 : Reg) ↦ᵣ dwordOf hsh q) **
        ⌜dwordOf recBytes q ≠ dwordOf hsh q⌝) **
        (((.x30 : Reg) ↦ᵣ cur) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
          bytesRegion cur recBytes ** bytesRegion hashPtr hsh ** FR)))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_pure_pre hmis)
  have hF := cpsBranchWithin_weaken
    (P := ⌜dwordOf recBytes q = dwordOf hsh q⌝ **
      (((.x5 : Reg) ↦ᵣ dwordOf recBytes q) ** ((.x6 : Reg) ↦ᵣ dwordOf hsh q) **
        ((.x30 : Reg) ↦ᵣ cur) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
        bytesRegion cur recBytes ** bytesRegion hashPtr hsh ** FR))
    (P' := ((((.x5 : Reg) ↦ᵣ dwordOf recBytes q) ** ((.x6 : Reg) ↦ᵣ dwordOf hsh q) **
        ⌜dwordOf recBytes q = dwordOf hsh q⌝) **
        (((.x30 : Reg) ↦ᵣ cur) ** ((.x10 : Reg) ↦ᵣ hashPtr) **
          bytesRegion cur recBytes ** bytesRegion hashPtr hsh ** FR)))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_pure_pre hhit)
  have hmerge := cpsBranchWithin_merge_branch_same_cr fC hT hF
  have hstep2 := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) fB hmerge
  have hstep1 := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) fA hstep2
  rw [show 1 + (1 + (1 + K)) = 2 + (1 + K) from by omega] at hstep1
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (fun _ hq => hq) hstep1


/-! ### The loop invariant and the routine's post -/

/-- The caller-visible resources the scan never touches. -/
private def ndlRest (retAddr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (cnt : Word) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr) **
  ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) ** ((.x31 : Reg) ↦ᵣ cnt) **
  (outP ↦ₘ o1) ** (outL ↦ₘ o2) ** (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)

private theorem ndlRest_pcFree (retAddr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (cnt : Word) :
    (ndlRest retAddr outP outL o1 o2 nodes cnt).pcFree := by
  unfold ndlRest; pcf

/-- **The loop invariant.** After `j` records, the cursor is at
    `dbBase + nodeDbSize (take j)`, the counter holds `count - j`, and NO
    record among the first `j` matched — the pure conjunct that makes the
    first match on exit the FIRST match overall. -/
private def ndlInv (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) (j : Nat) : Assertion :=
  ⌜nodeDbLookupSpec (nodes.take j) hsh = none⌝ **
  regOwn .x5 ** regOwn .x6 **
  ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))) **
  ((.x10 : Reg) ↦ᵣ hashPtr) ** bytesRegion hashPtr hsh **
  nodeDbIs dbBase nodes **
  ndlRest retAddr outP outL o1 o2 nodes (BitVec.ofNat 64 (nodes.length - j))

/-- The part of the routine's post that does not depend on hit/miss. -/
private def ndlQTail (retAddr hashPtr outP outL : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x6 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr) **
  ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
  bytesRegion hashPtr hsh ** (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length) **
  nodeDbIs dbBase nodes

private theorem ndlQTail_pcFree (retAddr hashPtr outP outL : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) :
    (ndlQTail retAddr hashPtr outP outL nodes hsh).pcFree := by
  unfold ndlQTail
  repeat first
    | apply pcFree_sepConj
    | exact pcFree_regOwn
    | exact pcFree_regIs
    | exact pcFree_memIs
    | exact bytesRegion_pcFree _ _
    | exact pcFree_nodeDbIs

/-- **The routine's post.** A hit pins `a0 = 0`, the out-pointer cell to the
    record's node-bytes address and the out-length cell to that node's
    length — two DIFFERENT cells holding two DIFFERENT quantities, so the
    claim is not symmetric in them. A miss pins `a0 = 1` and both cells
    UNCHANGED. -/
private def ndlQ (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) : Assertion :=
  (match nodeDbFind dbBase nodes hsh with
   | some (p, len) =>
       ((.x10 : Reg) ↦ᵣ (0 : Word)) ** (outP ↦ₘ p) ** (outL ↦ₘ BitVec.ofNat 64 len)
   | none =>
       ((.x10 : Reg) ↦ᵣ (1 : Word)) ** (outP ↦ₘ o1) ** (outL ↦ₘ o2)) **
  ndlQTail retAddr hashPtr outP outL nodes hsh

private theorem ndlQ_hit (retAddr hashPtr outP outL o1 o2 p : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) (len : Nat)
    (hf : nodeDbFind dbBase nodes hsh = some (p, len)) :
    ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh =
      ((((.x10 : Reg) ↦ᵣ (0 : Word)) ** (outP ↦ₘ p) **
        (outL ↦ₘ BitVec.ofNat 64 len)) **
        ndlQTail retAddr hashPtr outP outL nodes hsh) := by
  unfold ndlQ; rw [hf]

private theorem ndlQ_miss (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8))
    (hf : nodeDbFind dbBase nodes hsh = none) :
    ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh =
      ((((.x10 : Reg) ↦ᵣ (1 : Word)) ** (outP ↦ₘ o1) ** (outL ↦ₘ o2)) **
        ndlQTail retAddr hashPtr outP outL nodes hsh) := by
  unfold ndlQ; rw [hf]

/-- Strip an owned-register conjunct from a branch precondition. -/
private theorem cpsBranchWithin_regOwn_pre {n : Nat} {entry : Word} {cr : CodeReq}
    {r : Reg} {P : Assertion} {et ef : Word} {Qt Qf : Assertion}
    (h : ∀ v, cpsBranchWithin n entry cr ((r ↦ᵣ v) ** P) et Qt ef Qf) :
    cpsBranchWithin n entry cr (regOwn r ** P) et Qt ef Qf := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
  obtain ⟨ha, hb, hd2, hu2, ⟨v, hv⟩, hPb⟩ := hP1
  exact h v R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, ⟨ha, hb, hd2, hu2, hv, hPb⟩, hR2⟩ hpc


/-- `pcf` extended with the node-DB region. -/
local macro "pcf'" : tactic =>
  `(tactic| repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact pcFree_nodeDbIs)

/-- Strip two owned-register conjuncts from a branch precondition. -/
private theorem cpsBranchWithin_regOwn2_pre {n : Nat} {entry : Word} {cr : CodeReq}
    {r1 r2 : Reg} {P : Assertion} {et ef : Word} {Qt Qf : Assertion}
    (h : ∀ v1 v2, cpsBranchWithin n entry cr ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** P) et Qt ef Qf) :
    cpsBranchWithin n entry cr (regOwn r1 ** regOwn r2 ** P) et Qt ef Qf := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
  obtain ⟨ha, hb, hd2, hu2, ⟨v1, hv1⟩, hPb⟩ := hP1
  obtain ⟨hc, hdd, hd3, hu3, ⟨v2, hv2⟩, hPc⟩ := hPb
  exact h v1 v2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨ha, hb, hd2, hu2, hv1, hc, hdd, hd3, hu3, hv2, hPc⟩, hR2⟩ hpc

private theorem ent_regOwn2 (r1 r2 : Reg) (v1 v2 : Word) (P : Assertion)
    (h : PartialState) (hp : ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** P) h) :
    (regOwn r1 ** regOwn r2 ** P) h :=
  sepConj_mono (regIs_to_regOwn r1 v1)
    (sepConj_mono (regIs_to_regOwn r2 v2) (fun _ hx => hx)) h hp

private theorem ent_regOwn4 (r1 r2 r3 r4 : Reg) (v1 v2 v3 v4 : Word) (P : Assertion)
    (h : PartialState)
    (hp : ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) ** P) h) :
    (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** P) h :=
  sepConj_mono (regIs_to_regOwn r1 v1)
    (sepConj_mono (regIs_to_regOwn r2 v2)
      (sepConj_mono (regIs_to_regOwn r3 v3)
        (sepConj_mono (regIs_to_regOwn r4 v4) (fun _ hx => hx)))) h hp


/-! ### Round shapes

    The invariant with the record log split at the cursor, and the
    precondition each compare station is entered with. Both are stated as
    definitions so the round proof stays legible; each is definitionally the
    `**` chain the instruction lemmas produce. -/

/-- `ndlInv` with the record log split at record `j`, at invariant index `i`
    (`i = j` on entry to the round, `i = j + 1` on the loop-back exit). -/
private def ndlInvAt (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8))
    (n : List (BitVec 8)) (j i : Nat) : Assertion :=
  ⌜nodeDbLookupSpec (nodes.take i) hsh = none⌝ **
  regOwn .x5 ** regOwn .x6 **
  ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take i)))) **
  ((.x10 : Reg) ↦ᵣ hashPtr) ** bytesRegion hashPtr hsh **
  (nodeDbIs dbBase (nodes.take j) **
    (bytesRegion (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
        (nodeDbRecordBytes n) **
      nodeDbIs (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
        (nodes.drop (j + 1)))) **
  ndlRest retAddr outP outL o1 o2 nodes (BitVec.ofNat 64 (nodes.length - i))

/-- Everything a compare station leaves alone. -/
private def ndlFrame (retAddr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (j : Nat) : Assertion :=
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr) **
  ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
  ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (nodes.length - j)) **
  (outP ↦ₘ o1) ** (outL ↦ₘ o2) ** (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length) **
  nodeDbIs dbBase (nodes.take j) **
  nodeDbIs (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
    (nodes.drop (j + 1))

private theorem ndlFrame_pcFree (retAddr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (j : Nat) :
    (ndlFrame retAddr outP outL o1 o2 nodes j).pcFree := by
  unfold ndlFrame; pcf'

/-- The state at a compare station: dword `q` of the record under the cursor
    in `x5`, dword `q` of the caller's target hash in `x6`. -/
private def ndlSt (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8))
    (n : List (BitVec 8)) (j q : Nat) : Assertion :=
  ((.x5 : Reg) ↦ᵣ dwordOf (nodeDbRecordBytes n) q) **
  ((.x6 : Reg) ↦ᵣ dwordOf hsh q) **
  ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))) **
  ((.x10 : Reg) ↦ᵣ hashPtr) **
  bytesRegion (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
    (nodeDbRecordBytes n) **
  bytesRegion hashPtr hsh ** ndlFrame retAddr outP outL o1 o2 nodes j

private theorem cpsBranchWithin_unreachable {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {et ef : Word} {Qt Qf : Assertion}
    (h : ∀ hp, P hp → False) : cpsBranchWithin n entry cr P et Qt ef Qf := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
  exact absurd hP1 (h h1)

/-! ### One full round of the scan -/

private theorem ndlRound_spec (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8))
    (hhshLen : hsh.length = 32)
    (hkAll : ∀ m ∈ nodes, (Stateless.SpecRef.keccak256 m).length = 32)
    (hnAll : ∀ m ∈ nodes, m.length + 7 < 2 ^ 64)
    (hN : nodes.length < 2 ^ 64)
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr)
    (j : Nat) (hj : j < nodes.length) :
    cpsBranchWithin 20 (ndlB + 20) ndlCr
      (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j j)
      retAddr (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
      (ndlB + 20)
      (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1)) := by
  have hmem : nodes[j] ∈ nodes := List.getElem_mem hj
  have hk32 := hkAll _ hmem
  have hnlen := hnAll _ hmem
  have hlen40 := record_length_ge40 nodes[j] hk32
  have hd4 := dwordOf_record_len nodes[j] hk32 (by omega)
  have hx30 : (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
      + BitVec.ofNat 64 (nodeDbStride nodes[j])
      = dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))) := by
    rw [add_ofNat_add_ofNat, take_succ_snoc nodes j hj, nodeDbSize_snoc]
  have hcnt : (BitVec.ofNat 64 (nodes.length - j) : Word)
      = BitVec.ofNat 64 (nodes.length - (j + 1)) + 1 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1 : Word).toNat = 1 from by decide]
    omega
  have hx31 : (BitVec.ofNat 64 (nodes.length - j) : Word) - 1
      = BitVec.ofNat 64 (nodes.length - (j + 1)) := by
    rw [hcnt]; bv_omega
  have hcntne : (BitVec.ofNat 64 (nodes.length - j) : Word) ≠ (0 : Word) := by
    intro hc
    have := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from by decide] at this
    omega
  unfold ndlInvAt
  refine cpsBranchWithin_pure_pre (fun hnone => ?_)
  refine cpsBranchWithin_regOwn2_pre (fun v5 v6 => ?_)
  -- the mismatch continuation: bump the cursor, decrement, loop
  have hadv : ∀ q : Nat, q < 4 →
      dwordOf (nodeDbRecordBytes nodes[j]) q ≠ dwordOf hsh q →
      cpsBranchWithin 7 (ndlB + 96) ndlCr
        (ndlSt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j q)
        retAddr (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
        (ndlB + 20)
        (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1)) := by
    intro q hq hne
    have hkne : Stateless.SpecRef.keccak256 nodes[j] ≠ hsh :=
      ne_of_dword_ne (q := q)
        (by rwa [dwordOf_record_hash nodes[j] q hq hk32] at hne)
    have hnone' : nodeDbLookupSpec (nodes.take (j + 1)) hsh = none := by
      rw [take_succ_snoc nodes j hj]
      exact lookupSpec_none_snoc _ _ _ hnone hkne
    have hadvT := advanceTail_spec
      (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
      (BitVec.ofNat 64 (nodes.length - j)) (dwordOf hsh q)
      (nodeDbRecordBytes nodes[j]) nodes[j].length (nodeDbStride nodes[j])
      hlen40 hd4 hnlen rfl
    rw [hx30, hx31] at hadvT
    have hf := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ dwordOf (nodeDbRecordBytes nodes[j]) q) **
        ((.x10 : Reg) ↦ᵣ hashPtr) ** bytesRegion hashPtr hsh **
        nodeDbIs dbBase (nodes.take j) **
        nodeDbIs (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
          (nodes.drop (j + 1)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr) **
        ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
        (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
        (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) (by pcf') hadvT
    refine cpsTripleWithin_as_cpsBranchWithin_right retAddr _
      (cpsTripleWithin_weaken (fun _ hp => by
        unfold ndlSt ndlFrame at hp; xperm_hyp hp) (fun h hq2 => ?_) hf)
    show (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1)) h
    unfold ndlInvAt ndlRest
    refine (sepConj_pure_left h).mpr ⟨hnone', ?_⟩
    refine ent_regOwn2 .x5 .x6 (dwordOf (nodeDbRecordBytes nodes[j]) q)
      (BitVec.ofNat 64 (nodeDbStride nodes[j])) _ h ?_
    xperm_hyp hq2
  -- the hit continuation: publish node pointer and length, return 0
  have hhitB : (∀ q : Nat, q < 4 →
        dwordOf (nodeDbRecordBytes nodes[j]) q = dwordOf hsh q) →
      cpsBranchWithin 6 (ndlB + 72) ndlCr
        (ndlSt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j 3)
        retAddr (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
        (ndlB + 20)
        (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1)) := by
    intro heqs
    have hkeq : Stateless.SpecRef.keccak256 nodes[j] = hsh :=
      eq_of_dwords_eq hk32 hhshLen
        (fun q hq => by rw [← dwordOf_record_hash nodes[j] q hq hk32]; exact heqs q hq)
    have hfind : nodeDbFind dbBase nodes hsh =
        some ((dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) + (40 : Word),
          nodes[j].length) :=
      nodeDbFind_at dbBase nodes hsh j hj hnone hkeq
    have hT := hitTail_spec retAddr
      (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) outP outL hashPtr
      (dwordOf (nodeDbRecordBytes nodes[j]) 3) (dwordOf hsh 3) o1 o2
      (nodeDbRecordBytes nodes[j]) nodes[j].length hlen40 hd4 halign
    have hf := cpsTripleWithin_frameR
      (bytesRegion hashPtr hsh ** nodeDbIs dbBase (nodes.take j) **
        nodeDbIs (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
          (nodes.drop (j + 1)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (nodes.length - j)) **
        (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) (by pcf') hT
    refine cpsTripleWithin_as_cpsBranchWithin_left (ndlB + 20) _
      (cpsTripleWithin_weaken (fun _ hp => by
        unfold ndlSt ndlFrame at hp; xperm_hyp hp) (fun h hq2 => ?_) hf)
    show (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh) h
    rw [ndlQ_hit retAddr hashPtr outP outL o1 o2
      ((dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) + (40 : Word))
      nodes hsh nodes[j].length hfind]
    unfold ndlQTail
    rw [nodeDbIs_split_at dbBase nodes j hj]
    have hq3 : (((.x5 : Reg) ↦ᵣ
          ((dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) + (40 : Word))) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 nodes[j].length) **
        ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))) **
        ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (nodes.length - j)) **
        (((.x10 : Reg) ↦ᵣ (0 : Word)) **
          (outP ↦ₘ ((dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
            + (40 : Word))) **
          (outL ↦ₘ BitVec.ofNat 64 nodes[j].length) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr) **
          ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
          bytesRegion hashPtr hsh ** (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length) **
          nodeDbIs dbBase (nodes.take j) **
          bytesRegion (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
            (nodeDbRecordBytes nodes[j]) **
          nodeDbIs (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
            (nodes.drop (j + 1)))) h := by xperm_hyp hq2
    have hq4 := ent_regOwn4 .x5 .x6 .x30 .x31
      ((dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) + (40 : Word))
      (BitVec.ofNat 64 nodes[j].length)
      (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
      (BitVec.ofNat 64 (nodes.length - j)) _ h hq3
    xperm_hyp hq4
  -- the four compare stations, nested: each match falls through to the next,
  -- each mismatch jumps to the advance tail
  have hs0 := station_step 0 (ndlB + 24) (64 : BitVec 13)
    (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) hashPtr v5 v6 retAddr
    (nodeDbRecordBytes nodes[j]) hsh
    (ndlFrame retAddr outP outL o1 o2 nodes j)
    (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
    (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1))
    (ndlFrame_pcFree retAddr outP outL o1 o2 nodes j) 16
    (by omega) (by omega) (by decide)
    (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem)
    (fun hne => by
      rw [show (ndlB + 24 : Word) + 8 + signExtend13 (64 : BitVec 13) = ndlB + 96 from by
        rw [show signExtend13 (64 : BitVec 13) = (64 : Word) from by decide]; bv_omega]
      exact cpsBranchWithin_mono_nSteps (by omega) (hadv 0 (by omega) hne))
    (fun heq0 => by
      rw [show (ndlB + 24 : Word) + 12 = ndlB + 36 from by bv_omega]
      exact station_step 1 (ndlB + 36) (52 : BitVec 13)
        (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) hashPtr
        (dwordOf (nodeDbRecordBytes nodes[j]) 0) (dwordOf hsh 0) retAddr
        (nodeDbRecordBytes nodes[j]) hsh
        (ndlFrame retAddr outP outL o1 o2 nodes j)
        (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
        (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1))
        (ndlFrame_pcFree retAddr outP outL o1 o2 nodes j) 13
        (by omega) (by omega) (by decide)
        (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem)
        (fun hne => by
          rw [show (ndlB + 36 : Word) + 8 + signExtend13 (52 : BitVec 13) = ndlB + 96 from by
            rw [show signExtend13 (52 : BitVec 13) = (52 : Word) from by decide]; bv_omega]
          exact cpsBranchWithin_mono_nSteps (by omega) (hadv 1 (by omega) hne))
        (fun heq1 => by
          rw [show (ndlB + 36 : Word) + 12 = ndlB + 48 from by bv_omega]
          exact station_step 2 (ndlB + 48) (40 : BitVec 13)
            (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) hashPtr
            (dwordOf (nodeDbRecordBytes nodes[j]) 1) (dwordOf hsh 1) retAddr
            (nodeDbRecordBytes nodes[j]) hsh
            (ndlFrame retAddr outP outL o1 o2 nodes j)
            (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
            (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1))
            (ndlFrame_pcFree retAddr outP outL o1 o2 nodes j) 10
            (by omega) (by omega) (by decide)
            (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem)
            (by unfold ndlCr; code_mem)
            (fun hne => by
              rw [show (ndlB + 48 : Word) + 8 + signExtend13 (40 : BitVec 13) = ndlB + 96
                from by
                  rw [show signExtend13 (40 : BitVec 13) = (40 : Word) from by decide]
                  bv_omega]
              exact cpsBranchWithin_mono_nSteps (by omega) (hadv 2 (by omega) hne))
            (fun heq2 => by
              rw [show (ndlB + 48 : Word) + 12 = ndlB + 60 from by bv_omega]
              exact station_step 3 (ndlB + 60) (28 : BitVec 13)
                (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j))) hashPtr
                (dwordOf (nodeDbRecordBytes nodes[j]) 2) (dwordOf hsh 2) retAddr
                (nodeDbRecordBytes nodes[j]) hsh
                (ndlFrame retAddr outP outL o1 o2 nodes j)
                (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
                (ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1))
                (ndlFrame_pcFree retAddr outP outL o1 o2 nodes j) 7
                (by omega) (by omega) (by decide)
                (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem)
                (by unfold ndlCr; code_mem)
                (fun hne => by
                  rw [show (ndlB + 60 : Word) + 8 + signExtend13 (28 : BitVec 13)
                    = ndlB + 96 from by
                      rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
                      bv_omega]
                  exact hadv 3 (by omega) hne)
                (fun heq3 => by
                  rw [show (ndlB + 60 : Word) + 12 = ndlB + 72 from by bv_omega]
                  exact cpsBranchWithin_mono_nSteps (by omega)
                    (hhitB (fun q hq => by
                      interval_cases q
                      · exact heq0
                      · exact heq1
                      · exact heq2
                      · exact heq3))))))
  -- the loop guard `beq x31, x0, .miss`: with records left it is never taken
  have hbeq := cpsBranchWithin_extend_code (cr' := ndlCr)
    (by unfold ndlCr; code_mem)
    (beq_spec_gen_within .x31 .x0 (104 : BitVec 13)
      (BitVec.ofNat 64 (nodes.length - j)) (0 : Word) (ndlB + 20))
  have hbeqF := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))) **
      ((.x10 : Reg) ↦ᵣ hashPtr) **
      bytesRegion (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
        (nodeDbRecordBytes nodes[j]) **
      bytesRegion hashPtr hsh ** ((.x1 : Reg) ↦ᵣ retAddr) **
      ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
      (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
      (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length) **
      nodeDbIs dbBase (nodes.take j) **
      nodeDbIs (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
        (nodes.drop (j + 1))) (by pcf') hbeq
  have hmerge := cpsBranchWithin_merge_branch_same_cr hbeqF
    (cpsBranchWithin_unreachable (n := 19)
      (et := retAddr) (Qt := ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh)
      (ef := ndlB + 20)
      (Qf := ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j (j + 1))
      (fun _ hpp => by
        obtain ⟨_, _, _, _, hX, _⟩ := hpp
        obtain ⟨_, _, _, _, _, hBP⟩ := hX
        obtain ⟨_, _, _, _, _, hPure⟩ := hBP
        exact hcntne hPure.2))
    (cpsBranchWithin_weaken
      (P := ⌜(BitVec.ofNat 64 (nodes.length - j) : Word) ≠ (0 : Word)⌝ **
        (((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 (nodes.length - j)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
          ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))) **
          ((.x10 : Reg) ↦ᵣ hashPtr) **
          bytesRegion (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take j)))
            (nodeDbRecordBytes nodes[j]) **
          bytesRegion hashPtr hsh ** ((.x1 : Reg) ↦ᵣ retAddr) **
          ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
          (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
          (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length) **
          nodeDbIs dbBase (nodes.take j) **
          nodeDbIs (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take (j + 1))))
            (nodes.drop (j + 1))))
      (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_pure_pre (fun _ =>
        cpsBranchWithin_weaken (fun _ hp => by unfold ndlFrame; xperm_hyp hp)
          (fun _ hq => hq) (fun _ hq => hq) hs0)))
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_weaken (fun _ hp => by unfold ndlRest at hp; xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hmerge)


/-! ### From the invariant to the split form and back -/

private theorem ndlInv_eq_at (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) (j i : Nat)
    (hj : j < nodes.length) :
    ndlInv retAddr hashPtr outP outL o1 o2 nodes hsh i
      = ndlInvAt retAddr hashPtr outP outL o1 o2 nodes hsh nodes[j] j i := by
  unfold ndlInv ndlInvAt
  rw [nodeDbIs_split_at dbBase nodes j hj]

/-- Strip three owned-register conjuncts from a triple precondition. -/
private theorem cpsTripleWithin_regOwn3_pre {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 r3 : Reg} {P Q : Assertion}
    (h : ∀ v1 v2 v3, cpsTripleWithin n entry exit_ cr
      ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** P) Q) :
    cpsTripleWithin n entry exit_ cr (regOwn r1 ** regOwn r2 ** regOwn r3 ** P) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
  obtain ⟨a1, b1, d1, u1, ⟨v1, hv1⟩, hb1⟩ := hP1
  obtain ⟨a2, b2, d2, u2, ⟨v2, hv2⟩, hb2⟩ := hb1
  obtain ⟨a3, b3, d3, u3, ⟨v3, hv3⟩, hb3⟩ := hb2
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨a1, b1, d1, u1, hv1, a2, b2, d2, u2, hv2, a3, b3, d3, u3, hv3, hb3⟩, hR2⟩ hpc

/-- Strip two owned-register conjuncts from a triple precondition. -/
private theorem cpsTripleWithin_regOwn2_pre {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r1 r2 : Reg} {P Q : Assertion}
    (h : ∀ v1 v2, cpsTripleWithin n entry exit_ cr ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** P) Q) :
    cpsTripleWithin n entry exit_ cr (regOwn r1 ** regOwn r2 ** P) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
  obtain ⟨a1, b1, d1, u1, ⟨v1, hv1⟩, hb1⟩ := hP1
  obtain ⟨a2, b2, d2, u2, ⟨v2, hv2⟩, hb2⟩ := hb1
  exact h v1 v2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨a1, b1, d1, u1, hv1, a2, b2, d2, u2, hv2, hb2⟩, hR2⟩ hpc

/-! ### The exhaustion path (`idx 5 taken, 31, 32`) -/

private theorem ndlExh_spec (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8))
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr) :
    cpsTripleWithin 3 (ndlB + 20) retAddr ndlCr
      (ndlInv retAddr hashPtr outP outL o1 o2 nodes hsh nodes.length)
      (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh) := by
  unfold ndlInv ndlRest
  rw [show nodes.length - nodes.length = 0 from by omega,
    show (BitVec.ofNat 64 0 : Word) = (0 : Word) from by decide]
  refine cpsTripleWithin_pure_pre (fun hnone => ?_)
  refine cpsTripleWithin_regOwn2_pre (fun v5 v6 => ?_)
  have hmissF : nodeDbFind dbBase nodes hsh = none := by
    refine (nodeDbFind_none_iff dbBase nodes hsh).mpr ?_
    rwa [List.take_of_length_le (Nat.le_refl _)] at hnone
  -- idx 5: the guard fires
  have hbeq := cpsBranchWithin_extend_code (cr' := ndlCr)
    (by unfold ndlCr; code_mem)
    (beq_spec_gen_within .x31 .x0 (104 : BitVec 13) (0 : Word) (0 : Word) (ndlB + 20))
  rw [show (ndlB + 20 : Word) + signExtend13 (104 : BitVec 13) = ndlB + 124 from by
      rw [show signExtend13 (104 : BitVec 13) = (104 : Word) from by decide]; bv_omega,
    show (ndlB + 20 : Word) + 4 = ndlB + 24 from by bv_omega] at hbeq
  have hbeqF := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take nodes.length)))) **
      ((.x10 : Reg) ↦ᵣ hashPtr) ** bytesRegion hashPtr hsh **
      nodeDbIs dbBase nodes ** ((.x1 : Reg) ↦ᵣ retAddr) **
      ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
      (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
      (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) (by pcf') hbeq
  -- idx 31: li a0, 1
  have h31 := liftCode (cr' := ndlCr)
    (li_spec_gen_within .x10 hashPtr (1 : Word) (ndlB + 124) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show (ndlB + 124 : Word) + 4 = ndlB + 128 from by bv_omega] at h31
  -- idx 32: ret
  have h32 := liftCode (cr' := ndlCr)
    (EvmAsm.Evm64.ret_spec_within' (ndlB + 128) retAddr)
    (by unfold ndlCr; code_mem)
  rw [halign] at h32
  have f31 := cpsTripleWithin_frameR
    (((.x31 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take nodes.length)))) **
      bytesRegion hashPtr hsh ** nodeDbIs dbBase nodes **
      ((.x1 : Reg) ↦ᵣ retAddr) ** ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
      (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
      (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) (by pcf') h31
  have f32 := cpsTripleWithin_frameR
    (((.x31 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
      ((.x30 : Reg) ↦ᵣ (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take nodes.length)))) **
      ((.x10 : Reg) ↦ᵣ (1 : Word)) ** bytesRegion hashPtr hsh **
      nodeDbIs dbBase nodes ** ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
      (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
      (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) (by pcf') h32
  have htail := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) f31 f32
  have htA : cpsTripleWithin 2 (ndlB + 124) retAddr ndlCr
      ((((.x31 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ⌜(0 : Word) = (0 : Word)⌝) ** (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x30 : Reg) ↦ᵣ
          (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take nodes.length)))) **
        ((.x10 : Reg) ↦ᵣ hashPtr) ** bytesRegion hashPtr hsh **
        nodeDbIs dbBase nodes ** ((.x1 : Reg) ↦ᵣ retAddr) **
        ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
        (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
        (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)))
      (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh) := by
    rw [show (⌜(0 : Word) = (0 : Word)⌝ : Assertion) = empAssertion from by
      funext hh; simp [EvmAsm.Rv64.pure, empAssertion], sepConj_emp_right']
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) htail
    show (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh) h
    rw [ndlQ_miss retAddr hashPtr outP outL o1 o2 nodes hsh hmissF]
    unfold ndlQTail
    have hq3 : (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x30 : Reg) ↦ᵣ
          (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take nodes.length)))) **
        ((.x31 : Reg) ↦ᵣ (0 : Word)) **
        (((.x10 : Reg) ↦ᵣ (1 : Word)) ** (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr) **
          ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
          bytesRegion hashPtr hsh ** (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length) **
          nodeDbIs dbBase nodes)) h := by xperm_hyp hq
    have hq4 := ent_regOwn4 .x5 .x6 .x30 .x31 v5 v6
      (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take nodes.length))) (0 : Word) _ h hq3
    xperm_hyp hq4
  have hfaA : cpsTripleWithin 2 (ndlB + 24) retAddr ndlCr
      ((((.x31 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ⌜(0 : Word) ≠ (0 : Word)⌝) ** (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
        ((.x30 : Reg) ↦ᵣ
          (dbBase + BitVec.ofNat 64 (nodeDbSize (nodes.take nodes.length)))) **
        ((.x10 : Reg) ↦ᵣ hashPtr) ** bytesRegion hashPtr hsh **
        nodeDbIs dbBase nodes ** ((.x1 : Reg) ↦ᵣ retAddr) **
        ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
        (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
        (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)))
      (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh) := by
    refine cpsTripleWithin_unreachable (fun hpp hx => ?_)
    obtain ⟨_, _, _, _, hX, _⟩ := hx
    obtain ⟨_, _, _, _, _, hBP⟩ := hX
    obtain ⟨_, _, _, _, _, hPure⟩ := hBP
    exact hPure.2 rfl
  have hmerged := cpsBranchWithin_merge_same_cr hbeqF htA hfaA
  exact cpsTripleWithin_mono_nSteps (show (1 : Nat) + 2 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) hmerged)

/-! ### The whole scan loop -/

private theorem ndlLoop_spec (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8))
    (hhshLen : hsh.length = 32)
    (hkAll : ∀ m ∈ nodes, (Stateless.SpecRef.keccak256 m).length = 32)
    (hnAll : ∀ m ∈ nodes, m.length + 7 < 2 ^ 64)
    (hN : nodes.length < 2 ^ 64)
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr) :
    cpsTripleWithin (nodes.length * 20 + 3) (ndlB + 20) retAddr ndlCr
      (ndlInv retAddr hashPtr outP outL o1 o2 nodes hsh 0)
      (ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh) := by
  refine twoBreakRetLoop_spec nodes.length 20 3
    (ndlInv retAddr hashPtr outP outL o1 o2 nodes hsh) (fun i hi => ?_)
    (ndlExh_spec retAddr hashPtr outP outL o1 o2 nodes hsh halign)
  rw [ndlInv_eq_at retAddr hashPtr outP outL o1 o2 nodes hsh i i hi,
    ndlInv_eq_at retAddr hashPtr outP outL o1 o2 nodes hsh i (i + 1) hi]
  exact ndlRound_spec retAddr hashPtr outP outL o1 o2 nodes hsh hhshLen hkAll hnAll hN
    halign i hi

/-! ### The prologue (`idx 0..4`): materialize the count and the log base -/

private theorem ent_regOwn1 (r : Reg) (v : Word) (P : Assertion) (h : PartialState)
    (hp : ((r ↦ᵣ v) ** P) h) : (regOwn r ** P) h :=
  sepConj_mono (regIs_to_regOwn r v) (fun _ hx => hx) h hp

private theorem ndlProlog_spec (v5 v30 v31 : Word)
    (nodes : List (List (BitVec 8))) :
    cpsTripleWithin 5 ndlB (ndlB + 20) ndlCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
        (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length))
      (((.x5 : Reg) ↦ᵣ cntLoc) ** ((.x30 : Reg) ↦ᵣ dbBase) **
        ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 nodes.length) **
        (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) := by
  have hla1 := la_materialize_within .x5 v5 ndlB cntLoc (cr := ndlCr)
    (by decide) (by decide) (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem)
  have hld := liftCode (cr' := ndlCr)
    (ld_spec_gen_within .x31 .x5 cntLoc v31 (BitVec.ofNat 64 nodes.length)
      (0 : BitVec 12) (ndlB + 8) (by decide))
    (by unfold ndlCr; code_mem)
  rw [show cntLoc + signExtend12 (0 : BitVec 12) = cntLoc from by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (ndlB + 8 : Word) + 4 = ndlB + 12 from by bv_omega] at hld
  have hla2 := la_materialize_within .x30 v30 (ndlB + 12) dbBase (cr := ndlCr)
    (by decide) (by decide) (by unfold ndlCr; code_mem) (by unfold ndlCr; code_mem)
  rw [show (ndlB + 12 : Word) + 8 = ndlB + 20 from by bv_omega] at hla2
  have f1 := cpsTripleWithin_frameR
    (((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
      (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) (by pcf') hla1
  have f2 := cpsTripleWithin_frameR (((.x30 : Reg) ↦ᵣ v30)) (by pcf') hld
  have f3 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ cntLoc) ** ((.x31 : Reg) ↦ᵣ BitVec.ofNat 64 nodes.length) **
      (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length)) (by pcf') hla2
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f1 f2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 f3
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 + 2 ≤ 5 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c2)

/-! ## §7  The whole-routine triple -/

/-- The routine's ABI precondition: the four scratch registers owned, the
    three argument registers loaded, the two output cells owned, and the
    node DB the guest's `node_db_append` built. -/
def ndlPre (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) : Assertion :=
  regOwn .x5 ** regOwn .x30 ** regOwn .x31 ** regOwn .x6 **
  ((.x10 : Reg) ↦ᵣ hashPtr) ** ((.x11 : Reg) ↦ᵣ outP) ** ((.x12 : Reg) ↦ᵣ outL) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ retAddr) **
  (outP ↦ₘ o1) ** (outL ↦ₘ o2) ** bytesRegion hashPtr hsh **
  (cntLoc ↦ₘ BitVec.ofNat 64 nodes.length) ** nodeDbIs dbBase nodes

/-- The routine's postcondition, as a `match` on `nodeDbFind`: on a hit
    `a0 = 0`, `*a1` is the ABSOLUTE address of the matching record's node
    bytes and `*a2` is that node's length; on a miss `a0 = 1` and both
    output cells are unchanged. -/
def ndlPost (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) : Assertion :=
  ndlQ retAddr hashPtr outP outL o1 o2 nodes hsh

/-- **`node_db_lookup`, whole routine, at its linked guest address.**

    From the routine's entry `GuestAddrs.node_db_lookup`, over the emitted
    program `nodeDbLookup_prog` (`ndlCr = CodeReq.ofProg ndlB
    nodeDbLookup_prog`), execution returns to the caller in at most
    `5 + 20 * |nodes| + 3` steps with the `nodeDbFind` outcome published:
    a hit writes the node-bytes pointer to `*a1` and the node length to
    `*a2` and returns `a0 = 0`; a miss leaves both cells untouched and
    returns `a0 = 1`.

    All hypotheses are resource/ABI facts: a 32-byte target hash, 32-byte
    stored digests (the record layout `node_db_append` writes), u64-
    representable node lengths and record count, and a two-byte-aligned
    return address. There is NO input-domain gate: every DB and every target
    hash is inside the claim. -/
theorem node_db_lookup_spec_within (retAddr hashPtr outP outL o1 o2 : Word)
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8))
    (hhshLen : hsh.length = 32)
    (hkAll : ∀ m ∈ nodes, (Stateless.SpecRef.keccak256 m).length = 32)
    (hnAll : ∀ m ∈ nodes, m.length + 7 < 2 ^ 64)
    (hN : nodes.length < 2 ^ 64)
    (halign : (retAddr &&& ~~~(1 : Word)) = retAddr) :
    cpsTripleWithin (5 + (nodes.length * 20 + 3)) ndlB retAddr ndlCr
      (ndlPre retAddr hashPtr outP outL o1 o2 nodes hsh)
      (ndlPost retAddr hashPtr outP outL o1 o2 nodes hsh) := by
  unfold ndlPre ndlPost
  refine cpsTripleWithin_regOwn3_pre (fun v5 v30 v31 => ?_)
  have hpro := ndlProlog_spec v5 v30 v31 nodes
  have hproF := cpsTripleWithin_frameR
    (regOwn .x6 ** ((.x10 : Reg) ↦ᵣ hashPtr) ** ((.x11 : Reg) ↦ᵣ outP) **
      ((.x12 : Reg) ↦ᵣ outL) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ retAddr) ** (outP ↦ₘ o1) ** (outL ↦ₘ o2) **
      bytesRegion hashPtr hsh ** nodeDbIs dbBase nodes) (by pcf') hpro
  have hloop := ndlLoop_spec retAddr hashPtr outP outL o1 o2 nodes hsh hhshLen
    hkAll hnAll hN halign
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun h hq => ?_) hproF hloop)
  show (ndlInv retAddr hashPtr outP outL o1 o2 nodes hsh 0) h
  unfold ndlInv ndlRest
  rw [show nodes.take 0 = [] from List.take_zero, nodeDbSize_nil,
    show (BitVec.ofNat 64 0 : Word) = (0 : Word) from by decide,
    show dbBase + (0 : Word) = dbBase from by bv_omega,
    show nodes.length - 0 = nodes.length from by omega]
  refine (sepConj_pure_left h).mpr ⟨rfl, ?_⟩
  refine ent_regOwn1 .x5 cntLoc _ h ?_
  xperm_hyp hq

/-! ## §8  Non-vacuity, and the composition to the spec reference -/

/-- The hit arm is reachable for EVERY record: a record looked up by its own
    stored digest resolves to that record's node pointer. The first
    comparison succeeds by reflexivity, so no keccak evaluation is needed —
    the arm is inhabited, not merely unrefuted. -/
theorem nodeDbFind_head (base : Word) (n : List (BitVec 8))
    (rest : List (List (BitVec 8))) :
    nodeDbFind base (n :: rest) (Stateless.SpecRef.keccak256 n)
      = some (base + (40 : Word), n.length) := by
  rw [nodeDbFind_cons, if_pos rfl]

/-- ⭐ **A concrete satisfying instance of the whole-routine triple.**

    A closed instantiation: a one-record node DB holding the two-byte node
    `[0x02, 0x03]`, the caller's target hash equal to that record's stored
    digest, a return address of `0x80000100`, output cells at `0x2000` and
    `0x2008`. Every hypothesis of `node_db_lookup_spec_within` is discharged
    here, and the post is reduced to the HIT arm — so the theorem is not
    vacuously true on an empty precondition, and the branch that publishes
    the node pointer is the branch this instance takes. -/
theorem node_db_lookup_sample_witness :
    cpsTripleWithin 28 ndlB (0x80000100 : Word) ndlCr
      (ndlPre (0x80000100 : Word) (0x1000 : Word) (0x2000 : Word) (0x2008 : Word)
        (0 : Word) (0 : Word) [[0x02, 0x03]]
        (Stateless.SpecRef.keccak256 [0x02, 0x03]))
      ((((.x10 : Reg) ↦ᵣ (0 : Word)) **
          ((0x2000 : Word) ↦ₘ (dbBase + (40 : Word))) **
          ((0x2008 : Word) ↦ₘ BitVec.ofNat 64 2)) **
        ndlQTail (0x80000100 : Word) (0x1000 : Word) (0x2000 : Word) (0x2008 : Word)
          [[0x02, 0x03]] (Stateless.SpecRef.keccak256 [0x02, 0x03])) := by
  have h := node_db_lookup_spec_within (0x80000100 : Word) (0x1000 : Word)
    (0x2000 : Word) (0x2008 : Word) (0 : Word) (0 : Word) [[0x02, 0x03]]
    (Stateless.SpecRef.keccak256 [0x02, 0x03])
    (Stateless.SpecRef.keccak256_length _)
    (by
      intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      exact Stateless.SpecRef.keccak256_length _)
    (by decide) (by decide) (by decide)
  rw [ndlPost, ndlQ_hit _ _ _ _ _ _ _ _ _ _ (nodeDbFind_head dbBase [0x02, 0x03] [])] at h
  exact h

/-- **Machine ⇒ spec reference.** The length the routine publishes in `*a2`
    is the length of the node that `witness_state.py`'s
    `node_db : Dict[keccak256(entry), entry]` — ported as
    `Stateless.SpecRef.build_node_db` — maps the target hash to, and a
    machine miss is a `node_db` miss. The model↔reference leg was already
    closed by `nodeDbLookupSpec_eq_build_node_db`; this is the composition
    with the machine leg proved above. -/
theorem node_db_lookup_result_eq_build_node_db
    (nodes : List (List (BitVec 8))) (hsh : List (BitVec 8)) :
    (nodeDbFind dbBase nodes hsh).map Prod.snd
      = ((Stateless.SpecRef.build_node_db nodes).lookup hsh).map List.length :=
  nodeDbFind_eq_build_node_db dbBase nodes hsh

end EvmAsm.Codegen.NodeDbLookupSpec
