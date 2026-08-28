/-
  EvmAsm.Codegen.Programs.NodeDbAppendSpec

  **Whole-routine machine triple for the guest routine `node_db_append`**
  (GH #12318, the callee-composition lane; the append half of the node DB
  whose reader `node_db_lookup` is already rowed in
  `Codegen/Programs/NodeDbLookupSpec.lean`).

  `node_db_append` (`EvmAsm/Codegen/Programs/MptSetAcc.lean`, 48
  instructions) takes a freshly re-encoded MPT node at `a0` with length
  `a1`, hashes it with `zkvm_keccak256`, and appends the record

  ```
    keccak256(node)[32] | len:u64 LE | node[len] | zero pad to 8
  ```

  at `*mset_db_top`, bumping `*mset_db_top` by `40 + roundUp8 len` and
  `*mset_db_count` by one.

  ## What is proved here

  `node_db_append_spec_within` is a `cpsTripleWithin` anchored at
  `GuestAddrs.node_db_append` over

  ```
    ndaFullCode = ndaCr.union (ndaKeccakCode.union ndaMemcpyCode)
  ```

  where `ndaCr = CodeReq.ofProg (GuestAddrs.node_db_append) nodeDbAppend_prog`
  — the `guestImageEntries` pairing itself.  The two callee halves are the
  `guestImageEntries` pairings of `zkvm_keccak256` and `mset_memcpy`, so
  every one of the three components is an image claim; the union is
  *required*, because the routine's two `jal`s really do execute those two
  images and `callWithin_spec` needs them fetchable from one `CodeReq`.

  **Both callees are COMPOSED, not assumed**: the proof consumes the rowed
  `EvmAsm.Codegen.Proofs.zkvm_keccak256_spec_within` and the rowed
  `EvmAsm.Codegen.mset_memcpy_spec_within` through `callWithin_spec`, and
  `abiFrame_spec_own` discharges this routine's own prologue/epilogue.

  ## The post

  The post is stated in the `Evm64/MptAssertions.lean` node-DB vocabulary
  that was written for exactly this routine:

  * `nodeDbIs dbBase (nodes ++ [node])` — the record log GREW by one record,
    landing at `dbBase + nodeDbSize nodes` (via `nodeDbIs_snoc`), earlier
    records untouched;
  * `nodeDbTopIs` / `nodeDbCountIs` at `nodes ++ [node]` — the bump pointer
    and the record count both advanced;
  * the appended record's bytes are `nodeDbRecordBytes node`, whose hash
    field is `Stateless.SpecRef.keccak256 node` — the SPEC REFERENCE digest,
    not the guest's sponge model (`keccakBodyDigest_eq_specref` bridges it).

  This is the shape `node_db_lookup_spec_within` consumes, so the two halves
  of the node DB now meet: the `⚠️ NOT established here` caveat in the
  `node_db_lookup` registry row ("that `node_db_append` establishes the
  `nodeDbIs` shape this triple consumes") is what this module closes.

  ## What is NOT covered

  * No capacity guard.  The routine has none (see the `sd13v safety
    boundary` note on `nodeDbAppend_prog`), and neither does this triple:
    the caller must supply an unused `40 + roundUp8 len` window at
    `*mset_db_top`, which is what `bytesRegion topAddr hdr0` /
    `bytesRegion (topAddr + 40) dst0` in the precondition are.  Whether the
    8 MiB slab is large enough for a whole block is a separate obligation.
  * The pad bytes of the payload slot must ALREADY be zero
    (`hdst0pad`).  That is the arena invariant (`mset_db_data` is a
    `.zero` slab and `node_db_top` only ever advances), not something the
    routine establishes: it writes `len` bytes and leaves the rest.
  * Nothing about WHICH node the caller passes.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.NodeDbAppendBlocks
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.AccountBalanceHelperSpec
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Evm64.MptAssertions
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrameOwn
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.Tactics.XCancelStruct

-- ⚠️ Deliberately off, for the reason recorded in `AddressFromPubkeySpec.lean`:
-- keccak's scratch base `Zk3` is `private` in `HashBridgeKeccakTop`, and a bare
-- occurrence would otherwise be auto-bound as a fresh universally quantified
-- `Word`, silently turning a claim about the scratch arena into a claim about an
-- arbitrary region.
set_option autoImplicit false

namespace EvmAsm.Codegen.NodeDbAppendSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Evm64
open EvmAsm.Evm64.Terminating
open EvmAsm.Codegen.Proofs

open private Zk3 from EvmAsm.Codegen.Proofs.HashBridgeKeccakTop

/-! ## §8  The `zkvm_keccak256` call (index 11)

    ⭐ WHICH OF THE CALLEE'S SIDE CONDITIONS SURVIVE.  Of
    `zkvm_keccak256_spec_within`'s twenty hypotheses, the fourteen about its
    own 200-byte `zk3_state` scratch arena are facts about the LINKED LAYOUT
    and are discharged here (`decide` over the 136 reachable byte offsets,
    which `rem ≤ 135` bounds), not pushed onto callers.  Only the ones
    mentioning the CALLER's node pointer remain hypotheses — those a caller
    can actually satisfy. -/

private theorem zk3_toNat : Zk3.toNat = 2745483488 := by decide

set_option maxRecDepth 100000 in
/-- Every byte offset the sponge can touch on the `rem` tail (`rem ≤ 135`,
    so offsets `0..135`) is a valid byte access in the scratch arena. -/
private theorem zk3_valid_range :
    ∀ k, k < 136 → isValidByteAccess (Zk3 + BitVec.ofNat 64 k) = true := by decide

set_option maxRecDepth 100000 in
private theorem zk3_mem_range :
    ∀ j, j < 200 → isValidMemAddr (Zk3 + BitVec.ofNat 64 j) = true := by decide

set_option maxRecDepth 100000 in
/-- **Index 11: `jal ra, zkvm_keccak256`.**  On return `mset_db_hash` holds
    the digest of the node bytes, and `s0`/`s1` (the node pointer and its
    length) are intact because they are inside keccak's own callee-saved
    frame. -/
theorem nda_keccak_call_spec (spVal vRa nodePtr : Word)
    (node hash0 os : List (BitVec 8)) (N rem : Nat)
    (v18 v20 v28 v29 : Word) (A : Assertion) (hA : A.pcFree)
    (hlen : node.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hhash0 : hash0.length = 32)
    (hos : os.length = 200)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8i : (keccakAbsorbCursor nodePtr N).toNat % 8 = 0)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor nodePtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor nodePtr N + BitVec.ofNat 64 (rem - (n + 1))) = true) :
    cpsTripleWithin (1 + (5 + keccakBodyFuel N rem + 6))
        (ndaAt 11) (ndaAt 12) ndaFullCode
      (((.x1 : Reg) ↦ᵣ vRa) ** ((.x2 : Reg) ↦ᵣ spVal) **
        regsAt keccakFrame (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
        frameSlotsOwn keccakFrame (spVal + signExtend12 (-32 : BitVec 12)) **
        keccakCallerPre nodePtr (BitVec.ofNat 64 node.length) ndaHashLoc
          v28 v29 os node hash0 A)
      (((.x1 : Reg) ↦ᵣ (ndaAt 12)) ** ((.x2 : Reg) ↦ᵣ spVal) **
        regsAt keccakFrame (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
        frameSlotsSaved keccakFrame (spVal + signExtend12 (-32 : BitVec 12))
          (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
        keccakCallerPost nodePtr ndaHashLoc node N rem A) := by
  have hrem64 : rem < 2 ^ 64 := by omega
  have hcallee := zkvm_keccak256_spec_within spVal (ndaAt 12)
    nodePtr ndaHashLoc node N rem hash0
    nodePtr (BitVec.ofNat 64 node.length) v18 v20 v28 v29 os A hA
    (by decide) hlen hrem_le hhash0 hos
    (by decide) (by decide) hNbound hrem64
    hb8i
    (by intro n hn; rw [zk3_toNat]; omega)
    hoveri
    (by
      intro n hn
      exact zk3_valid_range (rem - (n + 1)) (by omega))
    hvalidi
    (by exact zk3_valid_range rem (by omega))
    (by exact zk3_valid_range 135 (by omega))
    zk3_mem_range
  rw [← hlen] at hcallee
  have hcalleeFull := cpsTripleWithin_extend_code nda_keccak_mem hcallee
  have hmem : ∀ a i, CodeReq.singleton (ndaAt 11) (.JAL .x1
      (Codegen.jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.node_db_append + 44)))
      a = some i → ndaFullCode a = some i :=
    ndaMemFull 11 _ (by decide) rfl
  have hcall := callWithin_spec (cr := ndaFullCode)
    (P := ((.x2 : Reg) ↦ᵣ spVal) **
      regsAt keccakFrame (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
      frameSlotsOwn keccakFrame (spVal + signExtend12 (-32 : BitVec 12)) **
      keccakCallerPre nodePtr (BitVec.ofNat 64 node.length) ndaHashLoc
        v28 v29 os node hash0 A)
    (Q := ((.x2 : Reg) ↦ᵣ spVal) **
      regsAt keccakFrame (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
      frameSlotsSaved keccakFrame (spVal + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
      keccakCallerPost nodePtr ndaHashLoc node N rem A)
    (ndaAt 11) ndaK vRa
    (Codegen.jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.node_db_append + 44))
    (5 + keccakBodyFuel N rem + 6)
    (by decide)
    hmem
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regsAt _ _)
        (pcFree_sepConj (pcFree_frameSlotsOwn _ _)
          (keccakCallerPre_pcFree _ _ _ _ _ _ _ _ _ hA))))
    (by
      rw [ndaAt_succ 11]
      exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
        (fun _ hq => by xcancel_struct hq) hcalleeFull)
  rw [ndaAt_succ 11] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hcall

/-! ## §9  The `mset_memcpy` call (index 29)

    The second composed callee.  Its eight hypotheses split cleanly: the
    DESTINATION half is about the record window the caller supplies, the
    SOURCE half about the node buffer.  Both are resource facts (alignment,
    in-bounds, no-wrap, valid access); none constrains the node's CONTENT. -/

set_option maxRecDepth 100000 in
/-- **Index 29: `jal ra, mset_memcpy`.**  Copies the node bytes into the
    record's payload field; the source region is pinned INTACT by the
    callee's own post, which is what lets the caller keep the node buffer. -/
theorem nda_memcpy_call_spec (nodePtr dstBase vRa : Word)
    (node dst0 : List (BitVec 8))
    (h_src_align : nodePtr.toNat % 8 = 0)
    (h_dst_align : dstBase.toNat % 8 = 0)
    (h_dst_bound : node.length ≤ dst0.length)
    (h_src_over : nodePtr.toNat + node.length < 2 ^ 64)
    (h_dst_over : dstBase.toNat + dst0.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < node.length →
      isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dst0.length →
      isValidByteAccess (dstBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (1 + (6 * node.length + 2)) (ndaAt 29) (ndaAt 30) ndaFullCode
      (((.x1 : Reg) ↦ᵣ vRa) **
        ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
        ((.x11 : Reg) ↦ᵣ nodePtr) ** ((.x10 : Reg) ↦ᵣ dstBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        bytesRegion nodePtr node ** bytesRegion dstBase dst0)
      (((.x1 : Reg) ↦ᵣ (ndaAt 30)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
        ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 node.length)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        bytesRegion nodePtr node **
        bytesRegion dstBase (copyIntoRegion dst0 node 0 0 node.length)) := by
  have hra : ((ndaAt 30) &&& ~~~(1 : Word)) = ndaAt 30 := by
    rw [show ndaAt 30 = ndaB + 120 from by unfold ndaAt; rfl]
    decide
  have hcallee := Codegen.mset_memcpy_spec_within nodePtr dstBase (ndaAt 30)
    node dst0 0 0 node.length
    h_src_align h_dst_align (by omega) (by omega) h_src_over h_dst_over
    h_src_valid h_dst_valid
  rw [hra] at hcallee
  rw [show (BitVec.ofNat 64 0 : Word) = 0 from rfl] at hcallee
  simp only [add_zero_word, Nat.zero_add] at hcallee
  have hcalleeFull := cpsTripleWithin_extend_code nda_memcpy_mem hcallee
  have hmem : ∀ a i, CodeReq.singleton (ndaAt 29) (.JAL .x1
      (Codegen.jalOff GuestAddrs.mset_memcpy (GuestAddrs.node_db_append + 116)))
      a = some i → ndaFullCode a = some i :=
    ndaMemFull 29 _ (by decide) rfl
  have hcall := callWithin_spec (cr := ndaFullCode)
    (P := ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
      ((.x11 : Reg) ↦ᵣ nodePtr) ** ((.x10 : Reg) ↦ᵣ dstBase) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      bytesRegion nodePtr node ** bytesRegion dstBase dst0)
    (Q := ((.x12 : Reg) ↦ᵣ (0 : Word)) **
      ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
      ((.x10 : Reg) ↦ᵣ (dstBase + BitVec.ofNat 64 node.length)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
      bytesRegion nodePtr node **
      bytesRegion dstBase (copyIntoRegion dst0 node 0 0 node.length))
    (ndaAt 29) msetMemcpyBase vRa
    (Codegen.jalOff GuestAddrs.mset_memcpy (GuestAddrs.node_db_append + 116))
    (6 * node.length + 2)
    (by decide)
    hmem
    (by pcFree)
    (by
      rw [ndaAt_succ 29]
      exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
        (fun _ hq => by xcancel_struct hq) hcalleeFull)
  rw [ndaAt_succ 29] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hcall

/-! ## §10  Three composite blocks

    The straight-line segments joined into the three blocks the whole-body
    proof chains: the record header (indices 12-25), the payload copy
    (26-29, containing the second call), and the publish (30-41). -/

/-- **Indices 12-25: the record header.**  Reads `*mset_db_top` into `s2`,
    then writes the four digest dwords and the length dword into the five
    header cells at the record cursor. -/
theorem nda_header_spec (topAddr lenW v5 v6 v7 v18 d0 d1 d2 d3 e0 e1 e2 e3 e4 : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 14 (ndaAt 12) (ndaAt 26) ndaCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        ((.x18 : Reg) ↦ᵣ v18) ** ((.x9 : Reg) ↦ᵣ lenW) **
        (ndaTopLoc ↦ₘ topAddr) **
        (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
        ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
        (topAddr ↦ₘ e0) ** ((topAddr + 8) ↦ₘ e1) ** ((topAddr + 16) ↦ₘ e2) **
        ((topAddr + 24) ↦ₘ e3) ** ((topAddr + 32) ↦ₘ e4) ** R)
      (((.x5 : Reg) ↦ᵣ ndaTopLoc) ** ((.x6 : Reg) ↦ᵣ ndaHashLoc) **
        ((.x7 : Reg) ↦ᵣ d3) ** ((.x18 : Reg) ↦ᵣ topAddr) ** ((.x9 : Reg) ↦ᵣ lenW) **
        (ndaTopLoc ↦ₘ topAddr) **
        (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
        ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
        (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) ** ((topAddr + 16) ↦ₘ d2) **
        ((topAddr + 24) ↦ₘ d3) ** ((topAddr + 32) ↦ₘ lenW) ** R) := by
  have a1 := nda_top_load_spec topAddr v5 v18
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x9 : Reg) ↦ᵣ lenW) **
      (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ e0) ** ((topAddr + 8) ↦ₘ e1) ** ((topAddr + 16) ↦ₘ e2) **
      ((topAddr + 24) ↦ₘ e3) ** ((topAddr + 32) ↦ₘ e4) ** R)
    (by pcf_r)
  have a2 := nda_hash_la_spec v6
    (((.x5 : Reg) ↦ᵣ ndaTopLoc) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x18 : Reg) ↦ᵣ topAddr) **
      ((.x9 : Reg) ↦ᵣ lenW) ** (ndaTopLoc ↦ₘ topAddr) **
      (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ e0) ** ((topAddr + 8) ↦ₘ e1) ** ((topAddr + 16) ↦ₘ e2) **
      ((topAddr + 24) ↦ₘ e3) ** ((topAddr + 32) ↦ₘ e4) ** R)
    (by pcf_r)
  have a3 := nda_hash_copy_spec topAddr v7 d0 d1 d2 d3 e0 e1 e2 e3
    (((.x5 : Reg) ↦ᵣ ndaTopLoc) ** ((.x9 : Reg) ↦ᵣ lenW) **
      (ndaTopLoc ↦ₘ topAddr) ** ((topAddr + 32) ↦ₘ e4) ** R)
    (by pcf_r)
  have a4 := nda_len_store_spec topAddr lenW e4
    (((.x5 : Reg) ↦ᵣ ndaTopLoc) ** ((.x6 : Reg) ↦ᵣ ndaHashLoc) ** ((.x7 : Reg) ↦ᵣ d3) **
      (ndaTopLoc ↦ₘ topAddr) **
      (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) ** ((topAddr + 16) ↦ₘ d2) **
      ((topAddr + 24) ↦ₘ d3) ** R)
    (by pcf_r)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) a1 a2
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 a3
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 a4
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c3

set_option maxRecDepth 100000 in
/-- **Indices 26-29: the payload copy.**  Sets up `mset_memcpy`'s three
    arguments and composes the callee's own contract. -/
theorem nda_copy_spec (topAddr nodePtr v10 v11 v12 vRa : Word)
    (node dst0 : List (BitVec 8))
    (h_src_align : nodePtr.toNat % 8 = 0)
    (h_dst_align : (topAddr + 40).toNat % 8 = 0)
    (h_dst_bound : node.length ≤ dst0.length)
    (h_src_over : nodePtr.toNat + node.length < 2 ^ 64)
    (h_dst_over : (topAddr + 40).toNat + dst0.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < node.length →
      isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dst0.length →
      isValidByteAccess ((topAddr + 40) + BitVec.ofNat 64 k) = true)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin (3 + (1 + (6 * node.length + 2))) (ndaAt 26) (ndaAt 30) ndaFullCode
      (regOwn .x5 **
        (((.x1 : Reg) ↦ᵣ vRa) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        ((.x8 : Reg) ↦ᵣ nodePtr) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion nodePtr node ** bytesRegion (topAddr + 40) dst0 ** R))
      (regOwn .x5 **
        (((.x1 : Reg) ↦ᵣ (ndaAt 30)) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        ((.x8 : Reg) ↦ᵣ nodePtr) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
        ((.x10 : Reg) ↦ᵣ ((topAddr + 40) + BitVec.ofNat 64 node.length)) **
        ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion nodePtr node **
        bytesRegion (topAddr + 40) (copyIntoRegion dst0 node 0 0 node.length) ** R)) := by
  have b1 := cpsTripleWithin_extend_code nda_wrapper_mem
    (nda_memcpy_args_spec topAddr nodePtr (BitVec.ofNat 64 node.length) v10 v11 v12
      (((.x1 : Reg) ↦ᵣ vRa) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 **
        bytesRegion nodePtr node ** bytesRegion (topAddr + 40) dst0 ** R)
      (by pcf_r))
  have b2 := cpsTripleWithin_frameR
    (((.x18 : Reg) ↦ᵣ topAddr) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
      ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) ** R)
    (by pcf_r)
    (nda_memcpy_call_spec nodePtr (topAddr + 40) vRa
      node dst0 h_src_align h_dst_align h_dst_bound h_src_over h_dst_over
      h_src_valid h_dst_valid)
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) b1 b2
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c1

/-- **Indices 30-41: publish.**  Bumps `*mset_db_top` by the record stride
    and `*mset_db_count` by one. -/
theorem nda_publish_spec (topAddr lenW v5 v6 v7 cnt : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 12 (ndaAt 30) (ndaAt 42) ndaCr
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        ((.x9 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        (ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) ** R)
      (((.x5 : Reg) ↦ᵣ ndaStrideWord lenW) ** ((.x6 : Reg) ↦ᵣ ndaCntLoc) **
        ((.x7 : Reg) ↦ᵣ (cnt + (1 : Word))) **
        ((.x9 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ (topAddr + ndaStrideWord lenW)) **
        (ndaTopLoc ↦ₘ (topAddr + ndaStrideWord lenW)) **
        (ndaCntLoc ↦ₘ (cnt + (1 : Word))) ** R) := by
  have c1 := nda_bump_spec topAddr lenW v5
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
      (ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) ** R)
    (by pcf_r)
  have c2 := nda_top_store_spec (topAddr + ndaStrideWord lenW) topAddr v6
    (((.x5 : Reg) ↦ᵣ ndaStrideWord lenW) ** ((.x9 : Reg) ↦ᵣ lenW) **
      ((.x7 : Reg) ↦ᵣ v7) ** (ndaCntLoc ↦ₘ cnt) ** R)
    (by pcf_r)
  have c3 := nda_count_bump_spec cnt ndaTopLoc v7
    (((.x5 : Reg) ↦ᵣ ndaStrideWord lenW) ** ((.x9 : Reg) ↦ᵣ lenW) **
      ((.x18 : Reg) ↦ᵣ (topAddr + ndaStrideWord lenW)) **
      (ndaTopLoc ↦ₘ (topAddr + ndaStrideWord lenW)) ** R)
    (by pcf_r)
  have j1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 c2
  have j2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) j1 c3
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) j2

/-! ## §11  The record header, as bytes

    The five dword cells the routine writes ARE the record's 40-byte header
    `keccak256(node) | len:u64 LE`. -/

/-- **The written header cells are the record header bytes.** -/
theorem record_header_join (topAddr : Word) (digest : List (BitVec 8)) (len : Nat)
    (hdig : digest.length = 32) (hlen : len < 2 ^ 64) :
    ((topAddr ↦ₘ packBytes (digest.take 8)) **
     ((topAddr + 8) ↦ₘ packBytes ((digest.drop 8).take 8)) **
     ((topAddr + 16) ↦ₘ packBytes ((digest.drop 16).take 8)) **
     ((topAddr + 24) ↦ₘ packBytes ((digest.drop 24).take 8)) **
     ((topAddr + 32) ↦ₘ BitVec.ofNat 64 len))
      = bytesRegion topAddr (digest ++ Stateless.SpecRef.natToBytesLE 8 len) := by
  have hc0 : (digest.take 8).length = 8 := by
    rw [List.length_take, hdig]; omega
  have hc1 : ((digest.drop 8).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hdig]; omega
  have hc2 : ((digest.drop 16).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hdig]; omega
  have hc3 : ((digest.drop 24).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hdig]; omega
  have hlenW : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat]; omega
  rw [region40_join topAddr (packBytes (digest.take 8))
    (packBytes ((digest.drop 8).take 8)) (packBytes ((digest.drop 16).take 8))
    (packBytes ((digest.drop 24).take 8)) (BitVec.ofNat 64 len)]
  rw [dwordBytes_packBytes _ hc0, dwordBytes_packBytes _ hc1,
    dwordBytes_packBytes _ hc2, dwordBytes_packBytes _ hc3,
    dwordBytes_eq_natToBytesLE, hlenW]
  congr 1
  exact congrArg (· ++ Stateless.SpecRef.natToBytesLE 8 len) (take_drop_32 digest hdig)

/-! ## §12  The block tail (indices 12-41)

    Everything after the keccak call, with the registers the callee returns
    as OWNERSHIP peeled to concrete values and the two byte windows
    (`mset_db_hash`'s digest, the record header slot) split into the dword
    cells the loads and stores act on. -/

/-- `nda_copy_spec` with `t0` supplied as a concrete value rather than bare
    ownership — the form the header block hands over. -/
theorem nda_copy_is_spec (topAddr nodePtr v5 v10 v11 v12 vRa : Word)
    (node dst0 : List (BitVec 8))
    (h_src_align : nodePtr.toNat % 8 = 0)
    (h_dst_align : (topAddr + 40).toNat % 8 = 0)
    (h_dst_bound : node.length ≤ dst0.length)
    (h_src_over : nodePtr.toNat + node.length < 2 ^ 64)
    (h_dst_over : (topAddr + 40).toNat + dst0.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < node.length →
      isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dst0.length →
      isValidByteAccess ((topAddr + 40) + BitVec.ofNat 64 k) = true)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin (3 + (1 + (6 * node.length + 2))) (ndaAt 26) (ndaAt 30) ndaFullCode
      (((.x5 : Reg) ↦ᵣ v5) **
        (((.x1 : Reg) ↦ᵣ vRa) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        ((.x8 : Reg) ↦ᵣ nodePtr) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion nodePtr node ** bytesRegion (topAddr + 40) dst0 ** R))
      (regOwn .x5 **
        (((.x1 : Reg) ↦ᵣ (ndaAt 30)) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        ((.x8 : Reg) ↦ᵣ nodePtr) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
        ((.x10 : Reg) ↦ᵣ ((topAddr + 40) + BitVec.ofNat 64 node.length)) **
        ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion nodePtr node **
        bytesRegion (topAddr + 40) (copyIntoRegion dst0 node 0 0 node.length) ** R)) :=
  cpsTripleWithin_weaken (sepConj_mono_left (regIs_to_regOwn .x5 v5)) (fun _ hq => hq)
    (nda_copy_spec topAddr nodePtr v10 v11 v12 vRa node dst0 h_src_align h_dst_align
      h_dst_bound h_src_over h_dst_over h_src_valid h_dst_valid R hR)

/-- `nda_publish_spec` with `t0` taken as bare ownership — the form
    `mset_memcpy`'s post hands back. -/
theorem nda_publish_own_spec (topAddr lenW v6 v7 cnt : Word)
    (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 12 (ndaAt 30) (ndaAt 42) ndaCr
      ((((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        ((.x9 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ topAddr) **
        (ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) ** R) ** regOwn .x5)
      (((.x5 : Reg) ↦ᵣ ndaStrideWord lenW) ** ((.x6 : Reg) ↦ᵣ ndaCntLoc) **
        ((.x7 : Reg) ↦ᵣ (cnt + (1 : Word))) **
        ((.x9 : Reg) ↦ᵣ lenW) ** ((.x18 : Reg) ↦ᵣ (topAddr + ndaStrideWord lenW)) **
        (ndaTopLoc ↦ₘ (topAddr + ndaStrideWord lenW)) **
        (ndaCntLoc ↦ₘ (cnt + (1 : Word))) ** R) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun vOld => ?_)
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp) (fun _ hq => hq)
    (nda_publish_spec topAddr lenW vOld v6 v7 cnt R hR)

set_option maxRecDepth 100000 in
/-- **Indices 12-41: everything after the keccak call.**  The record is
    written (header ‖ payload), the bump pointer advanced by the record
    stride, and the record count incremented. -/
theorem nda_tail_spec (nodePtr topAddr cnt v18 : Word)
    (node digest hdr0 dst0 : List (BitVec 8))
    (hdig : digest.length = 32) (hhdr : hdr0.length = 40)
    (hlenBound : node.length < 2 ^ 64)
    (h_src_align : nodePtr.toNat % 8 = 0)
    (h_dst_align : (topAddr + 40).toNat % 8 = 0)
    (h_dst_bound : node.length ≤ dst0.length)
    (h_src_over : nodePtr.toNat + node.length < 2 ^ 64)
    (h_dst_over : (topAddr + 40).toNat + dst0.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < node.length →
      isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dst0.length →
      isValidByteAccess ((topAddr + 40) + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (14 + (3 + (1 + (6 * node.length + 2))) + 12)
        (ndaAt 12) (ndaAt 42) ndaFullCode
      ((((.x1 : Reg) ↦ᵣ (ndaAt 12)) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) ** ((.x18 : Reg) ↦ᵣ v18) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion ndaHashLoc digest **
          (ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) **
          bytesRegion topAddr hdr0 ** bytesRegion (topAddr + 40) dst0 **
          bytesRegion nodePtr node)
        ** regOwns [(.x5 : Reg), .x6, .x7, .x11, .x12])
      (((.x1 : Reg) ↦ᵣ (ndaAt 30)) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
        ((.x18 : Reg) ↦ᵣ (topAddr + ndaStrideWord (BitVec.ofNat 64 node.length))) **
        ((.x10 : Reg) ↦ᵣ ((topAddr + 40) + BitVec.ofNat 64 node.length)) **
        ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ ndaStrideWord (BitVec.ofNat 64 node.length)) **
        ((.x6 : Reg) ↦ᵣ ndaCntLoc) ** ((.x7 : Reg) ↦ᵣ (cnt + (1 : Word))) **
        bytesRegion ndaHashLoc digest **
        (ndaTopLoc ↦ₘ (topAddr + ndaStrideWord (BitVec.ofNat 64 node.length))) **
        (ndaCntLoc ↦ₘ (cnt + (1 : Word))) **
        bytesRegion topAddr (digest ++ Stateless.SpecRef.natToBytesLE 8 node.length) **
        bytesRegion (topAddr + 40) (copyIntoRegion dst0 node 0 0 node.length) **
        bytesRegion nodePtr node) := by
  refine cpsTripleWithin_peel_regOwns [(.x5 : Reg), .x6, .x7, .x11, .x12]
    (by decide) (fun vf => ?_)
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  rw [region40_split topAddr hdr0 hhdr, region32_split ndaHashLoc digest hdig,
    ← record_header_join topAddr digest node.length hdig hlenBound]
  set lenW := BitVec.ofNat 64 node.length with hlenW
  set d0 := packBytes (digest.take 8) with hd0
  set d1 := packBytes ((digest.drop 8).take 8) with hd1
  set d2 := packBytes ((digest.drop 16).take 8) with hd2
  set d3 := packBytes ((digest.drop 24).take 8) with hd3
  -- header block (12-25)
  have t1 := cpsTripleWithin_extend_code nda_wrapper_mem
    (nda_header_spec topAddr lenW (vf .x5) (vf .x6) (vf .x7) v18 d0 d1 d2 d3
      (packBytes (hdr0.take 8)) (packBytes ((hdr0.drop 8).take 8))
      (packBytes ((hdr0.drop 16).take 8)) (packBytes ((hdr0.drop 24).take 8))
      (packBytes ((hdr0.drop 32).take 8))
      (((.x1 : Reg) ↦ᵣ (ndaAt 12)) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ vf .x11) ** ((.x12 : Reg) ↦ᵣ vf .x12) **
        (ndaCntLoc ↦ₘ cnt) ** bytesRegion (topAddr + 40) dst0 **
        bytesRegion nodePtr node)
      (by pcf_r))
  -- payload copy (26-29)
  have t2 := nda_copy_is_spec topAddr nodePtr ndaTopLoc (0 : Word) (vf .x11) (vf .x12)
    (ndaAt 12) node dst0 h_src_align h_dst_align h_dst_bound h_src_over h_dst_over
    h_src_valid h_dst_valid
    (((.x6 : Reg) ↦ᵣ ndaHashLoc) ** ((.x7 : Reg) ↦ᵣ d3) **
      (ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) **
      (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
      ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
      (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) ** ((topAddr + 16) ↦ₘ d2) **
      ((topAddr + 24) ↦ₘ d3) ** ((topAddr + 32) ↦ₘ lenW))
    (by pcf_r)
  -- publish (30-41)
  have t3 := cpsTripleWithin_extend_code nda_wrapper_mem
    (nda_publish_own_spec topAddr lenW ndaHashLoc d3 cnt
      (((.x1 : Reg) ↦ᵣ (ndaAt 30)) ** ((.x8 : Reg) ↦ᵣ nodePtr) **
        ((.x10 : Reg) ↦ᵣ ((topAddr + 40) + BitVec.ofNat 64 node.length)) **
        ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (ndaHashLoc ↦ₘ d0) ** ((ndaHashLoc + 8) ↦ₘ d1) **
        ((ndaHashLoc + 16) ↦ₘ d2) ** ((ndaHashLoc + 24) ↦ₘ d3) **
        (topAddr ↦ₘ d0) ** ((topAddr + 8) ↦ₘ d1) ** ((topAddr + 16) ↦ₘ d2) **
        ((topAddr + 24) ↦ₘ d3) ** ((topAddr + 32) ↦ₘ lenW) **
        bytesRegion nodePtr node **
        bytesRegion (topAddr + 40) (copyIntoRegion dst0 node 0 0 node.length))
      (by pcf_r))
  have j1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) t1 t2
  have j2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) j1 t3
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) j2

/-! ## §13  The whole body (indices 5-41)

    Argument setup, the keccak call, and the tail, joined.  The one seam
    worth naming is the INPUT REGION: `zkvm_keccak256`'s post hands the
    caller's buffer back SPLIT at the absorb cursor (`keccakCallerFreeA`
    exposes the consumed prefix and the residual separately), and
    `mset_memcpy` needs it as one region — so the two halves are rejoined
    here, at the seam the sponge left. -/

/-- The caller's input buffer, split at the absorb cursor exactly as
    `keccakCallerFreeA` leaves it. -/
theorem keccak_input_split (inputBase : Word) (input : List (BitVec 8)) (N : Nat)
    (hle : keccakAbsorbStep * N ≤ input.length) :
    bytesRegion inputBase input
      = (bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
         bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N)) := by
  have htk : (input.take (keccakAbsorbStep * N)).length = keccakAbsorbStep * N := by
    rw [List.length_take]; omega
  have h8 : (8 : Nat) ∣ (input.take (keccakAbsorbStep * N)).length := by
    rw [htk]; exact ⟨17 * N, by simp only [keccakAbsorbStep]; omega⟩
  have happ := bytesRegion_append inputBase (input.take (keccakAbsorbStep * N))
    (input.drop (keccakAbsorbStep * N)) h8
  rw [List.take_append_drop, htk] at happ
  rw [happ]
  rfl

/-- Four pinned registers weaken to four owned ones — the shape
    `abiFrame_spec_own`'s body post asks for (`regsOwnAt ndaFrame`), since
    the epilogue is about to overwrite all four from their frame slots. -/
private theorem own4 (r1 r2 r3 r4 : Reg) (w1 w2 w3 w4 : Word) :
    ∀ h, ((r1 ↦ᵣ w1) ** (r2 ↦ᵣ w2) ** (r3 ↦ᵣ w3) ** (r4 ↦ᵣ w4)) h →
      (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4) h :=
  sepConj_mono (regIs_to_regOwn r1 w1)
    (sepConj_mono (regIs_to_regOwn r2 w2)
      (sepConj_mono (regIs_to_regOwn r3 w3) (regIs_to_regOwn r4 w4)))

/-- Total step budget of the body: setup, the keccak call, and the tail. -/
def ndaBodySteps (N rem len : Nat) : Nat :=
  6 + (1 + (5 + keccakBodyFuel N rem + 6)) + (14 + (3 + (1 + (6 * len + 2))) + 12)

/-- The frame's entry valuation: `ra`, `s0`, `s1`, `s2`. -/
def ndaVals (ret v8 v9 v18 : Word) : Reg → Word
  | .x1 => ret
  | .x8 => v8
  | .x9 => v9
  | .x18 => v18
  | _ => (0 : Word)

theorem ndaVals_ra (ret v8 v9 v18 : Word) : ndaVals ret v8 v9 v18 .x1 = ret := rfl

/-- Caller-visible footprint at body entry, everything outside this
    routine's own frame. -/
def ndaCallerPre (newSp nodePtr topAddr cnt v12 v20 v28 v29 : Word)
    (node hash0 os hdr0 dst0 : List (BitVec 8)) (A : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ nodePtr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 node.length) **
  ((.x12 : Reg) ↦ᵣ v12) ** ((.x20 : Reg) ↦ᵣ v20) **
  ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwns keccakBodyFreeTemps **
  frameSlotsOwn keccakFrame (newSp + signExtend12 (-32 : BitVec 12)) **
  bytesRegion Zk3 os ** bytesRegion nodePtr node ** bytesRegion ndaHashLoc hash0 **
  (ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) **
  bytesRegion topAddr hdr0 ** bytesRegion (topAddr + 40) dst0 ** A

/-- Caller-visible footprint on return.  The three lines that matter are the
    appended record's bytes, the advanced bump pointer, and the incremented
    record count. -/
def ndaCallerPost (newSp nodePtr topAddr cnt v18 v20 : Word)
    (node dst0 : List (BitVec 8)) (N rem : Nat) (A : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ((topAddr + 40) + BitVec.ofNat 64 node.length)) **
  ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
  ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ v20) **
  ((.x5 : Reg) ↦ᵣ ndaStrideWord (BitVec.ofNat 64 node.length)) **
  ((.x6 : Reg) ↦ᵣ ndaCntLoc) ** ((.x7 : Reg) ↦ᵣ (cnt + (1 : Word))) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwns [(.x28 : Reg), .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17] **
  frameSlotsSaved keccakFrame (newSp + signExtend12 (-32 : BitVec 12))
    (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
  bytesRegion Zk3
    (setBytes (keccakGuestPad (keccakBodyPrePad node N rem) rem) 0
      (keccakBytes (keccakGuestPad (keccakBodyPrePad node N rem) rem) 0)) **
  bytesRegion nodePtr node **
  bytesRegion ndaHashLoc (Stateless.SpecRef.keccak256 node) **
  (ndaTopLoc ↦ₘ (topAddr + ndaStrideWord (BitVec.ofNat 64 node.length))) **
  (ndaCntLoc ↦ₘ (cnt + (1 : Word))) **
  bytesRegion topAddr (Stateless.SpecRef.keccak256 node ++
    Stateless.SpecRef.natToBytesLE 8 node.length) **
  bytesRegion (topAddr + 40) (copyIntoRegion dst0 node 0 0 node.length) ** A

theorem ndaCallerPre_pcFree (newSp nodePtr topAddr cnt v12 v20 v28 v29 : Word)
    (node hash0 os hdr0 dst0 : List (BitVec 8)) (A : Assertion) (hA : A.pcFree) :
    (ndaCallerPre newSp nodePtr topAddr cnt v12 v20 v28 v29
      node hash0 os hdr0 dst0 A).pcFree := by
  unfold ndaCallerPre
  pcf_r

theorem ndaCallerPost_pcFree (newSp nodePtr topAddr cnt v18 v20 : Word)
    (node dst0 : List (BitVec 8)) (N rem : Nat) (A : Assertion) (hA : A.pcFree) :
    (ndaCallerPost newSp nodePtr topAddr cnt v18 v20 node dst0 N rem A).pcFree := by
  unfold ndaCallerPost
  pcf_r

set_option maxRecDepth 100000 in
/-- **The whole body of `node_db_append`** — exactly what `abiFrame_spec_own`
    takes as its `hbody`. -/
theorem nda_body_spec (newSp ret nodePtr topAddr cnt : Word)
    (node hash0 os hdr0 dst0 : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v12 v18 v20 v28 v29 : Word) (A : Assertion) (hA : A.pcFree)
    (hlen : node.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hhash0 : hash0.length = 32)
    (hos : os.length = 200)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8i : (keccakAbsorbCursor nodePtr N).toNat % 8 = 0)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor nodePtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor nodePtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hhdr : hdr0.length = 40)
    (h_src_align : nodePtr.toNat % 8 = 0)
    (h_dst_align : (topAddr + 40).toNat % 8 = 0)
    (h_dst_bound : node.length ≤ dst0.length)
    (h_src_over : nodePtr.toNat + node.length < 2 ^ 64)
    (h_dst_over : (topAddr + 40).toNat + dst0.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < node.length →
      isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dst0.length →
      isValidByteAccess ((topAddr + 40) + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (ndaBodySteps N rem node.length) (ndaAt 5) (ndaAt 42) ndaFullCode
      (((.x2 : Reg) ↦ᵣ newSp) ** regsAt ndaFrame (ndaVals ret v8 v9 v18) **
        frameSlotsSaved ndaFrame newSp (ndaVals ret v8 v9 v18) **
        ndaCallerPre newSp nodePtr topAddr cnt v12 v20 v28 v29
          node hash0 os hdr0 dst0 A)
      (((.x2 : Reg) ↦ᵣ newSp) ** regsOwnAt ndaFrame **
        frameSlotsSaved ndaFrame newSp (ndaVals ret v8 v9 v18) **
        ndaCallerPost newSp nodePtr topAddr cnt v18 v20 node dst0 N rem A) := by
  have hlenBound : node.length < 2 ^ 64 := by omega
  have hdigest : keccakBodyDigest node N rem = Stateless.SpecRef.keccak256 node :=
    keccakBodyDigest_eq_specref node N rem hlen (by simp only [keccakAbsorbStep]; omega)
  have hdigLen : (Stateless.SpecRef.keccak256 node).length = 32 :=
    Stateless.SpecRef.keccak256_length node
  have hsplit := keccak_input_split nodePtr node N (by omega)
  have hAmbF : ((ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) **
      bytesRegion topAddr hdr0 ** bytesRegion (topAddr + 40) dst0 ** A).pcFree := by
    pcf_r
  -- indices 5-10
  have hsetup := cpsTripleWithin_extend_code nda_wrapper_mem
    (nda_setup_spec nodePtr (BitVec.ofNat 64 node.length) v8 v9 v12
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x2 : Reg) ↦ᵣ newSp) ** ((.x18 : Reg) ↦ᵣ v18) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns keccakBodyFreeTemps **
        frameSlotsOwn keccakFrame (newSp + signExtend12 (-32 : BitVec 12)) **
        frameSlotsSaved ndaFrame newSp (ndaVals ret v8 v9 v18) **
        bytesRegion Zk3 os ** bytesRegion nodePtr node **
        bytesRegion ndaHashLoc hash0 **
        ((ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) **
          bytesRegion topAddr hdr0 ** bytesRegion (topAddr + 40) dst0 ** A))
      (by pcf_r))
  -- index 11
  have hcall := cpsTripleWithin_frameR
    (frameSlotsSaved ndaFrame newSp (ndaVals ret v8 v9 v18))
    (pcFree_frameSlotsSaved _ _ _)
    (nda_keccak_call_spec newSp ret nodePtr node hash0 os N rem v18 v20 v28 v29
      ((ndaTopLoc ↦ₘ topAddr) ** (ndaCntLoc ↦ₘ cnt) **
        bytesRegion topAddr hdr0 ** bytesRegion (topAddr + 40) dst0 ** A)
      hAmbF hlen hrem_le hhash0 hos hNbound hb8i hoveri hvalidi)
  -- indices 12-41
  have htail := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) ** ((.x20 : Reg) ↦ᵣ v20) **
      regOwns [(.x28 : Reg), .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17] **
      frameSlotsSaved keccakFrame (newSp + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
      frameSlotsSaved ndaFrame newSp (ndaVals ret v8 v9 v18) **
      bytesRegion Zk3
        (setBytes (keccakGuestPad (keccakBodyPrePad node N rem) rem) 0
          (keccakBytes (keccakGuestPad (keccakBodyPrePad node N rem) rem) 0)) ** A)
    (by pcf_r)
    (nda_tail_spec nodePtr topAddr cnt v18 node (Stateless.SpecRef.keccak256 node)
      hdr0 dst0 hdigLen hhdr
      hlenBound h_src_align h_dst_align h_dst_bound h_src_over h_dst_over
      h_src_valid h_dst_valid)
  -- Present the tail's input region in the SPLIT form the sponge left it in,
  -- so the join across the call is a pure permutation.
  rw [hsplit] at htail
  -- Atomise every list-shaped assertion so the sep-conj normaliser can match
  -- atom for atom, then bridge the guest sponge to the spec reference.
  simp only [keccakCallerPre, keccakCallerPost, keccakCallerFreeA,
    keccakCsrsRestNoX5, keccakBodyFreeTemps, keccakFrame, keccakEntryVals,
    ndaFrame, ndaVals, ndaCallerPre, ndaCallerPost, regsAt_cons, regsAt_nil,
    regsOwnAt_cons, regsOwnAt_nil, regOwns_cons, regOwns_nil,
    frameSlotsOwn, frameSlotsSaved, List.foldr,
    sepConj_emp_right'] at hsetup hcall htail ⊢
  rw [hdigest] at hcall
  have j1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp)
    hsetup hcall
  have j2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp)
    j1 htail
  refine cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun h hq => ?_) j2
  -- Rejoin the input region: the caller sees one buffer again.
  rw [hsplit]
  refine sepConj_mono_right (sepConj_mono_left
    (own4 .x1 .x8 .x9 .x18 (ndaAt 30) nodePtr (BitVec.ofNat 64 node.length)
      (topAddr + ndaStrideWord (BitVec.ofNat 64 node.length)))) h ?_
  xcancel_struct hq

/-! ## §14  The whole routine -/

/-- 8-alignment of the record cursor carries to the payload field. -/
theorem align_add40 (topAddr : Word) (h : topAddr.toNat % 8 = 0) :
    (topAddr + 40).toNat % 8 = 0 := by
  have h40 : (40 : Word).toNat = 40 := by decide
  have hadd : (topAddr + 40).toNat = (topAddr.toNat + 40) % 2 ^ 64 := by
    rw [BitVec.toNat_add, h40]
  rw [hadd]
  omega

set_option maxRecDepth 100000 in
/-- **`node_db_append`, whole-routine triple at the guest entry.**

    Anchored at `GuestAddrs.node_db_append` over
    `ndaFullCode = ndaCr.union (ndaKeccakCode.union ndaMemcpyCode)` — this
    routine's own `guestImageEntries` pairing together with the two callee
    images its `jal`s really execute.  Both callees are COMPOSED (their own
    whole-routine triples are consumed through `callWithin_spec`), not
    assumed.

    The contract, in one line: given a node buffer at `a0` with length `a1`
    and an unused `40 + roundUp8 len` window at `*mset_db_top`, the window
    ends up holding `keccak256(node) ‖ len:u64 LE ‖ node ‖ zero pad`, the
    bump pointer advances by exactly that stride, and the record count
    increments — with the digest stated against `SpecRef.keccak256`, not the
    guest's own sponge model. -/
theorem node_db_append_spec_within (sp0 ret nodePtr topAddr cnt : Word)
    (node hash0 os hdr0 dst0 : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v12 v18 v20 v28 v29 : Word) (A : Assertion) (hA : A.pcFree)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : node.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hhash0 : hash0.length = 32)
    (hos : os.length = 200)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8i : (keccakAbsorbCursor nodePtr N).toNat % 8 = 0)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor nodePtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor nodePtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hhdr : hdr0.length = 40)
    (h_src_align : nodePtr.toNat % 8 = 0)
    (h_top_align : topAddr.toNat % 8 = 0)
    (h_dst_bound : node.length ≤ dst0.length)
    (h_src_over : nodePtr.toNat + node.length < 2 ^ 64)
    (h_dst_over : (topAddr + 40).toNat + dst0.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < node.length →
      isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dst0.length →
      isValidByteAccess ((topAddr + 40) + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin
        (1 + ndaFrame.length + ndaBodySteps N rem node.length
          + ndaFrame.length + 1 + 1)
        ndaB ret ndaFullCode
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt ndaFrame (ndaVals ret v8 v9 v18) **
        frameSlotsOwn ndaFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        ndaCallerPre (sp0 + signExtend12 (-32 : BitVec 12)) nodePtr topAddr cnt
          v12 v20 v28 v29 node hash0 os hdr0 dst0 A)
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt ndaFrame (ndaVals ret v8 v9 v18) **
        frameSlotsSaved ndaFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (ndaVals ret v8 v9 v18) **
        ndaCallerPost (sp0 + signExtend12 (-32 : BitVec 12)) nodePtr topAddr cnt
          v18 v20 node dst0 N rem A) := by
  refine abiFrame_spec_own ndaB sp0 ret (-32 : BitVec 12) (32 : BitVec 12)
    ndaFrame (0 : BitVec 12)
    [(.x8, (8 : BitVec 12)), (.x9, (16 : BitVec 12)), (.x18, (24 : BitVec 12))]
    (ndaVals ret v8 v9 v18) ndaBody _ _ _ ndaFullCode
    ndaFrame_cons ndaFrame_ne_zero (by decide) ?_ (ndaVals_ra ret v8 v9 v18) halign
    (ndaFrame_restore sp0)
    (ndaCallerPre_pcFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA)
    (ndaCallerPost_pcFree _ _ _ _ _ _ _ _ _ _ _ hA)
    ?_ ?_
  · rw [← nodeDbAppend_prog_eq_abiFrame, nodeDbAppend_prog_length]
    decide
  · intro a i h
    exact nda_wrapper_mem a i (by rwa [← nodeDbAppend_prog_eq_abiFrame] at h)
  · have hentry : ndaB + BitVec.ofNat 64 (4 * (1 + ndaFrame.length)) = ndaAt 5 := by
      rw [ndaFrame_length]; rfl
    have hexit : ndaB + BitVec.ofNat 64 (4 * (1 + ndaFrame.length + ndaBody.length))
        = ndaAt 42 := by
      rw [ndaFrame_length, ndaBody_length]; rfl
    rw [hentry, hexit]
    exact nda_body_spec (sp0 + signExtend12 (-32 : BitVec 12)) ret nodePtr topAddr cnt
      node hash0 os hdr0 dst0 N rem v8 v9 v12 v18 v20 v28 v29 A hA
      hlen hrem_le hhash0 hos hNbound hb8i hoveri hvalidi hhdr
      h_src_align (align_add40 topAddr h_top_align) h_dst_bound h_src_over h_dst_over
      h_src_valid h_dst_valid

/-! ## §15  The node-DB form

    The same triple, restated in the `Evm64/MptAssertions.lean` vocabulary
    the reader `node_db_lookup_spec_within` consumes: the record log GROWS
    by one node.  This is the statement the `node_db_lookup` registry row
    names as "⚠️ NOT established here". -/

/-- `ndaStrideWord` is the record stride `MptAssertions` computes. -/
theorem ndaStrideWord_eq_nodeDbStride (node : List (BitVec 8))
    (hlt : node.length + 7 < 2 ^ 64) :
    ndaStrideWord (BitVec.ofNat 64 node.length) = BitVec.ofNat 64 (nodeDbStride node) := by
  have hru := roundUp8_eq_alignToDword node.length hlt
  have h7 : BitVec.ofNat 64 node.length + (7 : Word)
      = BitVec.ofNat 64 (node.length + 7) := by
    rw [← ndaOfNat_add]; rfl
  unfold ndaStrideWord
  rw [h7, show ((BitVec.ofNat 64 (node.length + 7)) &&& ~~~(7 : Word))
        = alignToDword (BitVec.ofNat 64 (node.length + 7)) from rfl, ← hru,
    show (40 : Word) = BitVec.ofNat 64 40 from rfl, ndaOfNat_add]
  congr 1
  unfold nodeDbStride
  omega

/-- The record's bytes split at the header/payload seam the routine writes
    on either side of. -/
theorem record_bytes_split (topAddr : Word) (node : List (BitVec 8)) :
    bytesRegion topAddr (nodeDbRecordBytes node)
      = (bytesRegion topAddr (Stateless.SpecRef.keccak256 node ++
            Stateless.SpecRef.natToBytesLE 8 node.length) **
         bytesRegion (topAddr + 40)
            (node ++ List.replicate (roundUp8 node.length - node.length) 0)) := by
  have hhdrLen : (Stateless.SpecRef.keccak256 node ++
      Stateless.SpecRef.natToBytesLE 8 node.length).length = 40 := by
    rw [List.length_append, Stateless.SpecRef.keccak256_length]
    simp only [Stateless.SpecRef.natToBytesLE, List.length_map, List.length_range]
  rw [nodeDbRecordBytes_split, bytesRegion_append topAddr _ _ (by rw [hhdrLen]; exact ⟨5, rfl⟩),
    hhdrLen]
  rfl

/-- Caller-visible footprint on return, in node-DB vocabulary. -/
def ndaDbPost (newSp nodePtr dbBase v18 v20 : Word)
    (node : List (BitVec 8)) (nodes : List (List (BitVec 8)))
    (N rem : Nat) (A : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ ((dbBase + BitVec.ofNat 64 (nodeDbSize nodes) + 40) +
    BitVec.ofNat 64 node.length)) **
  ((.x11 : Reg) ↦ᵣ (nodePtr + BitVec.ofNat 64 node.length)) **
  ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x20 : Reg) ↦ᵣ v20) **
  ((.x5 : Reg) ↦ᵣ ndaStrideWord (BitVec.ofNat 64 node.length)) **
  ((.x6 : Reg) ↦ᵣ ndaCntLoc) **
  ((.x7 : Reg) ↦ᵣ (BitVec.ofNat 64 nodes.length + (1 : Word))) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwns [(.x28 : Reg), .x29, .x30, .x31, .x13, .x14, .x15, .x16, .x17] **
  frameSlotsSaved keccakFrame (newSp + signExtend12 (-32 : BitVec 12))
    (keccakEntryVals nodePtr (BitVec.ofNat 64 node.length) v18 v20) **
  bytesRegion Zk3
    (setBytes (keccakGuestPad (keccakBodyPrePad node N rem) rem) 0
      (keccakBytes (keccakGuestPad (keccakBodyPrePad node N rem) rem) 0)) **
  bytesRegion nodePtr node **
  bytesRegion ndaHashLoc (Stateless.SpecRef.keccak256 node) **
  nodeDbTopIs ndaTopLoc dbBase (nodes ++ [node]) **
  nodeDbCountIs ndaCntLoc (nodes ++ [node]) **
  nodeDbIs dbBase (nodes ++ [node]) ** A

set_option maxRecDepth 100000 in
/-- **`node_db_append` grows the record log by one node.**

    The same whole-routine triple as `node_db_append_spec_within`,
    instantiated at a record log `nodes` starting at `dbBase` and restated
    in the `nodeDbIs` / `nodeDbTopIs` / `nodeDbCountIs` vocabulary.  The
    appended record lands at `dbBase + nodeDbSize nodes` — the address the
    routine computes from `*mset_db_top` — with the earlier records
    untouched (`nodeDbIs_snoc`).

    ⚠️ The payload slot's PAD BYTES must already be zero (`hdst0pad`).  That
    is the append arena's invariant — `mset_db_data` is a `.zero` slab and
    `*mset_db_top` only ever advances — not something this routine
    establishes: it writes `len` bytes and leaves the rest alone. -/
theorem node_db_append_grows_db (sp0 ret nodePtr dbBase : Word)
    (node hash0 os hdr0 dst0 : List (BitVec 8))
    (nodes : List (List (BitVec 8))) (N rem : Nat)
    (v8 v9 v12 v18 v20 v28 v29 : Word) (A : Assertion) (hA : A.pcFree)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : node.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hhash0 : hash0.length = 32)
    (hos : os.length = 200)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hb8i : (keccakAbsorbCursor nodePtr N).toNat % 8 = 0)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor nodePtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor nodePtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hhdr : hdr0.length = 40)
    (hdst0len : dst0.length = roundUp8 node.length)
    (hdst0pad : dst0.drop node.length
      = List.replicate (roundUp8 node.length - node.length) 0)
    (h_src_align : nodePtr.toNat % 8 = 0)
    (h_top_align : (dbBase + BitVec.ofNat 64 (nodeDbSize nodes)).toNat % 8 = 0)
    (h_src_over : nodePtr.toNat + node.length < 2 ^ 64)
    (h_dst_over : ((dbBase + BitVec.ofNat 64 (nodeDbSize nodes)) + 40).toNat
      + dst0.length < 2 ^ 64)
    (h_src_valid : ∀ k, k < node.length →
      isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true)
    (h_dst_valid : ∀ k, k < dst0.length →
      isValidByteAccess
        (((dbBase + BitVec.ofNat 64 (nodeDbSize nodes)) + 40) + BitVec.ofNat 64 k)
          = true) :
    cpsTripleWithin
        (1 + ndaFrame.length + ndaBodySteps N rem node.length
          + ndaFrame.length + 1 + 1)
        ndaB ret ndaFullCode
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt ndaFrame (ndaVals ret v8 v9 v18) **
        frameSlotsOwn ndaFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        ndaCallerPre (sp0 + signExtend12 (-32 : BitVec 12)) nodePtr
          (dbBase + BitVec.ofNat 64 (nodeDbSize nodes))
          (BitVec.ofNat 64 nodes.length) v12 v20 v28 v29 node hash0 os hdr0 dst0
          (nodeDbIs dbBase nodes ** A))
      (((.x2 : Reg) ↦ᵣ sp0) ** regsAt ndaFrame (ndaVals ret v8 v9 v18) **
        frameSlotsSaved ndaFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (ndaVals ret v8 v9 v18) **
        ndaDbPost (sp0 + signExtend12 (-32 : BitVec 12)) nodePtr dbBase v18 v20
          node nodes N rem A) := by
  have hlenLt : node.length < 2 ^ 63 := by omega
  have hru : node.length ≤ roundUp8 node.length := by
    unfold roundUp8; omega
  have hmain := node_db_append_spec_within sp0 ret nodePtr
    (dbBase + BitVec.ofNat 64 (nodeDbSize nodes)) (BitVec.ofNat 64 nodes.length)
    node hash0 os hdr0 dst0 N rem v8 v9 v12 v18 v20 v28 v29
    (nodeDbIs dbBase nodes ** A) (pcFree_sepConj pcFree_nodeDbIs hA)
    halign hlen hrem_le hhash0 hos hNbound hb8i hoveri hvalidi hhdr
    h_src_align h_top_align (by omega) h_src_over h_dst_over h_src_valid h_dst_valid
  -- The copied payload: the node bytes, then the pad the arena already held.
  have hcopy : copyIntoRegion dst0 node 0 0 node.length
      = node ++ List.replicate (roundUp8 node.length - node.length) 0 := by
    rw [copyIntoRegion_prefix dst0 node (by omega), hdst0pad]
  -- The bump pointer lands at `dbBase + nodeDbSize (nodes ++ [node])`.
  have htop : (dbBase + BitVec.ofNat 64 (nodeDbSize nodes))
        + ndaStrideWord (BitVec.ofNat 64 node.length)
      = dbBase + BitVec.ofNat 64 (nodeDbSize (nodes ++ [node])) := by
    rw [ndaStrideWord_eq_nodeDbStride node (by omega), BitVec.add_assoc,
      ndaOfNat_add, nodeDbSize_snoc]
  -- The record count.
  have hcnt : BitVec.ofNat 64 nodes.length + (1 : Word)
      = BitVec.ofNat 64 (nodes ++ [node]).length := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ndaOfNat_add, List.length_append]
    rfl
  simp only [ndaCallerPost, ndaDbPost, nodeDbTopIs, nodeDbCountIs,
    nodeDbIs_snoc, record_bytes_split, hcopy, htop, hcnt] at hmain ⊢
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hmain

/-! ## §16  Non-vacuity

    The triple carries a twenty-hypothesis bundle, so "no input-domain
    gate" is a claim that has to be checked in BOTH directions, and neither
    is readable off the tier constructor:

    * the bundle must be **satisfiable**, else the theorem says nothing —
      `nodeDbAppend_precondition_reachable` exhibits a witness for the
      input-dependent half, and `node_db_append_sample_witness` is a CLOSED
      instantiation of the whole triple at numeric addresses (its mere
      elaboration is the evidence: if any hypothesis were unsatisfiable at
      every instantiation, no such term could exist);
    * the bundle must not be **trivially true**, else "resource/ABI only"
      would be a statement about a vacuous restriction — the three negative
      controls exhibit instantiations at which the same conjuncts are
      provably FALSE. -/

/-- A concrete four-byte node (a short RLP list), in the writable RAM zone
    at an 8-aligned base. -/
private def ndaSampleNode : List (BitVec 8) := [0xc3, 0x82, 0x01, 0x02]

private def ndaSampleNodePtr : Word := (0xa0000000 : Word)

/-- The append arena's base for the witness: a distinct 8-aligned RAM
    address, so the record window and the node buffer are genuinely
    disjoint regions rather than an unsatisfiable overlap. -/
private def ndaSampleDbBase : Word := (0xa0000100 : Word)

/-- ⭐ **The input-dependent hypotheses are satisfiable.**  `N = 0`,
    `rem = 4` at an aligned RAM base discharges the length partition, the
    absorb-cursor alignment, the payload-slot geometry and every
    `rem`-indexed overflow / validity obligation — on a node that is
    genuinely nonempty. -/
theorem nodeDbAppend_precondition_reachable :
    ∃ (nodePtr dbBase : Word) (node dst0 : List (BitVec 8)) (N rem : Nat),
      node ≠ [] ∧
      node.length = keccakAbsorbStep * N + rem ∧
      rem ≤ 135 ∧
      keccakAbsorbStep * N + rem < 2 ^ 63 ∧
      (keccakAbsorbCursor nodePtr N).toNat % 8 = 0 ∧
      nodePtr.toNat % 8 = 0 ∧
      dbBase.toNat % 8 = 0 ∧
      dst0.length = roundUp8 node.length ∧
      dst0.drop node.length
        = List.replicate (roundUp8 node.length - node.length) 0 ∧
      (∀ n, n < rem →
        (keccakAbsorbCursor nodePtr N).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (keccakAbsorbCursor nodePtr N + BitVec.ofNat 64 (rem - (n + 1)))
          = true) ∧
      (∀ k, k < node.length →
        isValidByteAccess (nodePtr + BitVec.ofNat 64 k) = true) ∧
      (∀ k, k < dst0.length →
        isValidByteAccess ((dbBase + 40) + BitVec.ofNat 64 k) = true) := by
  refine ⟨ndaSampleNodePtr, ndaSampleDbBase, ndaSampleNode,
    List.replicate 8 (0 : BitVec 8), 0, 4,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro n hn; interval_cases n <;> decide
  · intro n hn; interval_cases n <;> decide
  · intro k hk
    have hk' : k < 4 := by simpa [ndaSampleNode] using hk
    interval_cases k <;> decide
  · intro k hk
    have hk' : k < 8 := by simpa using hk
    interval_cases k <;> decide

set_option maxRecDepth 100000 in
/-- ⭐ **A closed instantiation of the whole-routine triple**: the empty
    node DB at `ndaSampleDbBase` gains its first record, the four-byte node
    at `ndaSampleNodePtr`.  Every data hypothesis is discharged by `decide`
    at numeric addresses; only the caller's stack pointer, return address
    (with its two-byte alignment) and the callee-saved incumbents stay
    parameters, since nothing in the bundle constrains them.

    Cited by the `node_db_append` registry row as its non-vacuity witness. -/
noncomputable abbrev node_db_append_sample_witness
    (sp0 ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret)
    (v8 v9 v12 v18 v20 v28 v29 : Word) :=
  node_db_append_grows_db sp0 ret ndaSampleNodePtr ndaSampleDbBase
    ndaSampleNode (List.replicate 32 (0 : BitVec 8)) (List.replicate 200 (0 : BitVec 8))
    (List.replicate 40 (0 : BitVec 8)) (List.replicate 8 (0 : BitVec 8))
    [] 0 4 v8 v9 v12 v18 v20 v28 v29 empAssertion pcFree_emp
    halign (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro n hn; interval_cases n <;> decide)
    (by intro n hn; interval_cases n <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
    (by
      intro k hk
      have hk' : k < 4 := by simpa [ndaSampleNode] using hk
      interval_cases k <;> decide)
    (by
      intro k hk
      have hk' : k < 8 := by simpa using hk
      interval_cases k <;> decide)

/-- ⛔ **Negative control 1** — the 8-alignment premise is a REAL
    restriction, not a tautology about every address: one byte past the
    sample base it is provably false.  So the triple is genuinely partial
    over its argument types, and the row must not be read as total. -/
theorem nodeDbAppend_align_bites :
    ¬ ((0xa0000001 : Word).toNat % 8 = 0) := by decide

/-- ⛔ **Negative control 2** — the byte-validity premise excludes
    addresses: one outside every memory zone fails `isValidByteAccess`, so
    the `h_src_valid` / `h_dst_valid` families are not vacuously true. -/
theorem nodeDbAppend_validity_negative_control :
    isValidByteAccess (0x90000000 : Word) = false := by decide

/-- ⛔ **Negative control 3**, on the one CONTENT-shaped premise: the
    payload slot's pad bytes really must already be zero.  A slot whose pad
    holds `0xff` falsifies `hdst0pad` — which is why that hypothesis is an
    arena invariant the caller must carry, not something this routine
    establishes. -/
theorem nodeDbAppend_pad_zero_bites :
    ¬ ((List.replicate 8 (0xff : BitVec 8)).drop 4
        = List.replicate (roundUp8 4 - 4) 0) := by decide

end EvmAsm.Codegen.NodeDbAppendSpec

