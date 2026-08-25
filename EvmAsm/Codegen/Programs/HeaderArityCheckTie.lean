/-
  EvmAsm.Codegen.Programs.HeaderArityCheckTie

  Shared-exit and dispatch contracts for `header_extended_decode_arity_check`
  (GH #12799, ownership-table row 5).

  ## Extent, DERIVED from the linked image (not taken from prose)

  `nm gen-out/regionmap/stateless_guest.elf`, restricted to `t/T/w/W`, sorted
  numerically, `hi` = the next symbol:

  ```
  000000008000bb28 t rlp_walk_next_leaf
  000000008000bb64 t header_extended_decode
  000000008000be1c t header_extended_decode_arity_check   <- lo
  000000008000bff0 t headers_parent_hash                  <- hi
  000000008000c078 t header_validate_parent_hash
  ```

  `hi - lo = 0x1d4 = 468` bytes ⇒ `468 / 4 = 117` instructions, and
  `headerExtendedDecodeArityCheck_prog.length * 4 = 117 * 4 = 468`.
  **Cross-check ✅** (`arity_length` below is the kernel-checked half).

  ⛔ #12799's body says 194.  That figure spans THREE symbols
  (`header_extended_decode_arity_check` 117 + `headers_parent_hash` 34 +
  `header_validate_parent_hash` 43 = 194); it was re-derived here from `nm`
  before anything was proved, and 117 is the routine.

  ## Shape

  One backward transfer, `+412 -> +112`: a loop over the header's RLP fields,
  indexed by `s5`, bounded by the item count `s4`.  Everything else is forward.

  ```
  +0    .. +32   prologue: open 96-byte frame, spill ra, s0..s6
  +36   .. +52   move the two arguments into s0/s1, point a2 at the count slot
  +56            jal rlp_list_count_items            (prog idx 14)
  +60            bnez a0        -> +424 FAIL
  +64            ld s4,64(sp)   -- the item count
  +68   .. +72   reload the two arguments
  +76            jal rlp_walk_init                   (prog idx 19)
  +80            bnez a2        -> +424 FAIL
  +84   .. +88   s2/s3 := walk cursor / walk end
  +92   .. +104  arity gate: s4 = 21, else s4 = 23, else -> +424 FAIL
  +108           li s5,0
  +112           beq s5,s4      -> +416 OK                    <-- LOOP HEADER
  +116  .. +120  a0/a1 := s2/s3
  +124           jal rlp_walk_next_leaf              (prog idx 31)
  +128           bnez a1        -> +424 FAIL
  +132           sub s6,a0,a2   -- content start = new cursor - reported length
  +136           mv  s2,a0      -- advance the walk cursor
  +140  .. +312  22-probe dispatch on s5 (this module's `dispatch_probe_within`)
  +316           j              -> +408   (no check for this field index)
  +320  .. +328  length arm, expect 32
  +332  .. +340  length arm, expect 20
  +344  .. +352  length arm, expect 256
  +356  .. +364  length arm, expect 8
  +368  .. +384  jal rlp_content_to_u64_strict       (prog idx 94)
  +388  .. +404  jal rlp_content_to_u256_be_strict   (prog idx 100)
  +408           addi s5,s5,1
  +412           j              -> +112               <-- the only back edge
  +416  .. +420  li a0,0 ; j -> +428                  OK exit
  +424           li a0,1                              FAIL exit (10 branches)
  +428  .. +464  epilogue: reload s6..s0, ra; close the frame; ret
  ```

  ## ⭐ What this module FACTORS out of the 34-branch fan-in

  Four convergence points carry 34 branches between them.  None of them is
  proved per-branch here; each is ONE lemma with N instantiations.

  | fan-in target | branches | factored as | instantiations |
  |---|---|---|---|
  | `+424` FAIL   | 10 | `fail_exit_spec_within` (on `epilogue_spec_within`) | 1 lemma, 10 users |
  | `+320/332/344/356` | 4 arms reached by 4 branches (+ 10 probes into `+320`) | `len_check_arm_within` | 1 lemma, 4 instantiations |
  | `+368`        |  8 | one dispatch target of `dispatch_probe_within` | — |
  | `+408` join   |  6 | `dispatchTarget`'s default arm | — |
  | 22 dispatch probes | 22 | `dispatch_probe_within` | 1 lemma, 22 `rfl`-discharged instantiations |

  The epilogue at `+428` is proved **once** and instantiated **twice** — once
  under `+424` (`a0 = 1`) and once under `+416` (`a0 = 0`).  Between them the
  two exit stubs are what all 10 failure branches and the single success branch
  actually reach, so the "10 separate failure proofs" the shape suggests are one
  proof used ten times.

  The 22 dispatch probes are two instructions each (`li t0,K` ⨾ `beq s5,t0,T`)
  and differ only in `(K, T)`.  `dispatch_probe_within` is stated over the pair,
  taking the two code lookups as hypotheses; each of the 22 instantiations
  discharges them as kernel-checked `rfl`s — 44 lookups, no repeated reasoning.
  `dispatchTarget` turns the 22-way branch into a SINGLE-exit triple whose exit
  PC is a computed function of `s5`, so there is no 23-way case split anywhere.

  ## Frame — every register read off the disassembly

  `addi sp,sp,-96` at `+0` and `addi sp,sp,96` at `+460`: not a leaf, 96-byte
  frame.  Callee-saved registers, with the line each was read from:

  | reg   | role                            | saved / restored |
  |-------|---------------------------------|------------------|
  | `x1`  | `ra`, caller return address     | `+4  sd ra,0(sp)`    / `+456 ld ra,0(sp)` |
  | `x8`  | `s0`, header pointer arg        | `+8  sd s0,8(sp)`    / `+452 ld s0,8(sp)`  ; set `+36 mv s0,a0` |
  | `x9`  | `s1`, header length arg         | `+12 sd s1,16(sp)`   / `+448 ld s1,16(sp)` ; set `+40 mv s1,a1` |
  | `x18` | `s2`, walk cursor               | `+16 sd s2,24(sp)`   / `+444 ld s2,24(sp)` ; set `+84 mv s2,a0`, `+136 mv s2,a0` |
  | `x19` | `s3`, walk end pointer          | `+20 sd s3,32(sp)`   / `+440 ld s3,32(sp)` ; set `+88 mv s3,a1` |
  | `x20` | `s4`, RLP item count            | `+24 sd s4,40(sp)`   / `+436 ld s4,40(sp)` ; set `+64 ld s4,64(sp)` |
  | `x21` | `s5`, loop index                | `+28 sd s5,48(sp)`   / `+432 ld s5,48(sp)` ; set `+108 li s5,0`, `+408 addi s5,s5,1` |
  | `x22` | `s6`, content start pointer     | `+32 sd s6,56(sp)`   / `+428 ld s6,56(sp)` ; set `+132 sub s6,a0,a2` |

  Caller-saved registers this routine itself touches: `x5` (`t0`, every `li`
  in the dispatch and in the four length arms), `x10`/`x11`/`x12` (`a0`/`a1`/
  `a2`, the call ABI).  `x12` is additionally used as an OUT-pointer twice
  (`+52 addi a2,sp,64` and `+396 addi a2,sp,64`).

  ⭐ Frame slot `sp+64` is used for **two** different things: `rlp_list_count_items`
  writes the item count there (read back at `+64`), and the `rlp_content_to_u256_be_strict`
  arm reuses the same 32 bytes (`sp+64 .. sp+95`) as its output buffer.  The
  96-byte frame is exactly `64` bytes of spills plus that `32`-byte scratch.

  ## ⛔ The non-LIST gate is INHERITED here, not discharged

  `rlp_walk_next_leaf`'s contract
  (`RlpWalkNextLeafTie.rlp_walk_next_leaf_entry_nonlist_strict_spec_within`,
  `.conditional`) is gated on the prefix byte at the walk cursor being `< 0xc0`.
  The same finding as on `header_extended_decode` (#12835) holds here, and it
  was checked against the instructions rather than assumed:

  * the call at `+124` is preceded by exactly `+116 mv a0,s2` and `+120 mv a1,s3`
    — two register moves, **no load of any kind**, so nothing in this routine
    ever inspects the byte at the cursor before calling;
  * the only test on the call's result is `+128 bnez a1`, on the returned
    STATUS, after the fact;
  * the 22-probe dispatch that follows tests `s5` (the loop index) and the four
    length arms test `a2` (the reported content length).  Neither is the prefix
    byte, and neither is evaluated before the call.

  ⇒ the gate SURVIVES into row 5, and, as #12835 already recorded for row 6,
  into row 7 and into **#12776** downstream.  No instruction in
  `header_extended_decode_arity_check` discharges it.

  ## What is NOT proved here, named rather than glossed

  There is **no whole-routine triple** for `header_extended_decode_arity_check`
  in this module, and the blocker is the one #12835 named for row 6, in its
  harder form.  Closing the loop needs an invariant that re-establishes
  `rlp_walk_next_leaf`'s ENTRY premises (`hoff`, `hvalid`, `hlt`, `hss`, `hls`,
  and `hnotlist`) for iteration `i+1` from the `rlpItemDecodeStrictW` post of
  iteration `i`.  That walk-post ⇒ walk-pre derivation does not exist at any
  level of the stack; on row 6 the 19 sites are straight-line and could be rowed
  one at a time without it, but here the sites are the SAME site under a loop,
  so there is no per-site fallback.  The loop's measure is settled
  (`(s4 - s5 : Nat)`, strictly decreasing at `+408` under the `+112` guard
  `s5 ≠ s4`); the invariant's memory component is what is missing.

  Also not covered here: the frame prologue (`+0 .. +88`, including the two
  calls at `+56` and `+76`) and the two callee arms (`+368`, `+400`) as composed
  triples.  What IS covered of the loop is its control skeleton only:
  `arity_gate_within` (`+92 .. +104`), `loop_guard_within` (`+112`),
  `loop_backedge_within` (`+408 .. +412`) and `loop_measure_decreases`.  Those
  settle termination; they do not settle the invariant.
-/
import EvmAsm.Codegen.Programs.HeaderDecode
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Codegen.HeaderArityCheckTie

open EvmAsm.Rv64

/-- Guest entry of the 117-instruction `header_extended_decode_arity_check`
    (`GuestAddrs.header_extended_decode_arity_check = 0x8000be1c`). -/
abbrev L : Word := (GuestAddrs.header_extended_decode_arity_check : Word)

/-- The linked image of the routine, anchored at its own `GuestAddrs` entry.
    Paired with `GuestAddrs.header_extended_decode_arity_check` in
    `guestImageEntries` (`GuestImageEntries.lean:270`). -/
abbrev arityCode : CodeReq := CodeReq.ofProg L headerExtendedDecodeArityCheck_prog

/-- Kernel-checked half of the extent cross-check: `117 * 4 = 468` against
    `GuestAddrs.headers_parent_hash - GuestAddrs.header_extended_decode_arity_check`
    read off the symbol table.  See the module docstring. -/
theorem arity_length : headerExtendedDecodeArityCheck_prog.length = 117 := rfl

/-- The other half, on the addresses themselves: the next symbol in the sorted
    `nm` output is `headers_parent_hash`, and the gap is exactly the program. -/
theorem arity_extent :
    GuestAddrs.headers_parent_hash - GuestAddrs.header_extended_decode_arity_check
      = 4 * headerExtendedDecodeArityCheck_prog.length := by
  rw [arity_length]; decide

/-! ## Point lookups into the linked image.

    Every instruction this module cites is pulled out of `arityCode` by index,
    with the index-to-address arithmetic and the list projection both discharged
    by kernel evaluation.  `arity_sub_at` is the form the block lemmas want: a
    `CodeReq.singleton ⊆ arityCode` inclusion. -/

theorem arity_at (k : Nat) (hk : k < 117) (addr : Word)
    (haddr : addr = L + BitVec.ofNat 64 (4 * k)) :
    arityCode addr
      = some (headerExtendedDecodeArityCheck_prog.get ⟨k, by rw [arity_length]; exact hk⟩) :=
  CodeReq.ofProg_lookup_addr L headerExtendedDecodeArityCheck_prog k addr
    (by rw [arity_length]; exact hk) (by rw [arity_length]; norm_num) haddr

theorem arity_sub_at (k : Nat) (hk : k < 117) (addr : Word) (i : Instr)
    (haddr : addr = L + BitVec.ofNat 64 (4 * k))
    (hi : headerExtendedDecodeArityCheck_prog.get ⟨k, by rw [arity_length]; exact hk⟩ = i) :
    ∀ a' i', CodeReq.singleton addr i a' = some i' → arityCode a' = some i' :=
  CodeReq.singleton_mono (by rw [← hi]; exact arity_at k hk addr haddr)

/-- `pcf` closes `P.pcFree` for the atoms used in this module. -/
local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure)

/-! ## ⭐ The shared exit: one epilogue, ten failure branches, one success branch.

    `+428 .. +464` is the only `ret` in the routine.  It is proved once, below,
    and every one of the eleven transfers that leaves the loop reaches it
    through one of the two two-instruction stubs at `+416` and `+424`. -/

/-- Registers and frame cells the epilogue restores, at the moment it is
    entered.  `q` is the frame base (`sp` AFTER `+0 addi sp,sp,-96`); the caller
    entered the routine with `x2 = q + 96`. -/
abbrev epiPre (q raIn s0In s1In s2In s3In s4In s5In s6In : Word)
    (v1 v8 v9 v18 v19 v20 v21 v22 : Word) : Assertion :=
  (.x2 ↦ᵣ q) ** (.x1 ↦ᵣ v1) **
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
  (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
  (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0In) ** ((q + 16) ↦ₘ s1In) **
  ((q + 24) ↦ₘ s2In) ** ((q + 32) ↦ₘ s3In) ** ((q + 40) ↦ₘ s4In) **
  ((q + 48) ↦ₘ s5In) ** ((q + 56) ↦ₘ s6In)

/-- The caller-visible state after the epilogue: every callee-saved register
    back to its entry value, `sp` back up, `ra` restored. -/
abbrev epiPost (q raIn s0In s1In s2In s3In s4In s5In s6In : Word) : Assertion :=
  (.x2 ↦ᵣ (q + 96)) ** (.x1 ↦ᵣ raIn) **
  (.x8 ↦ᵣ s0In) ** (.x9 ↦ᵣ s1In) ** (.x18 ↦ᵣ s2In) ** (.x19 ↦ᵣ s3In) **
  (.x20 ↦ᵣ s4In) ** (.x21 ↦ᵣ s5In) ** (.x22 ↦ᵣ s6In) **
  (q ↦ₘ raIn) ** ((q + 8) ↦ₘ s0In) ** ((q + 16) ↦ₘ s1In) **
  ((q + 24) ↦ₘ s2In) ** ((q + 32) ↦ₘ s3In) ** ((q + 40) ↦ₘ s4In) **
  ((q + 48) ↦ₘ s5In) ** ((q + 56) ↦ₘ s6In)

/-- **The shared epilogue** (`+428 .. +464`, prog idx 107..116, 10 instructions):
    reload `s6,s5,s4,s3,s2,s1,s0,ra`, close the 96-byte frame, `ret`.

    Proved ONCE.  `fail_exit_spec_within` and `ok_exit_spec_within` are its two
    users, and between them they are what all 34 branches of the fan-in
    ultimately reach. -/
theorem epilogue_spec_within (q raIn s0In s1In s2In s3In s4In s5In s6In : Word)
    (v1 v8 v9 v18 v19 v20 v21 v22 : Word) :
    cpsTripleWithin 10 (L + 428) (raIn &&& ~~~1) arityCode
      (epiPre q raIn s0In s1In s2In s3In s4In s5In s6In v1 v8 v9 v18 v19 v20 v21 v22)
      (epiPost q raIn s0In s1In s2In s3In s4In s5In s6In) := by
  have e56 : q + signExtend12 (56 : BitVec 12) = q + 56 := by
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide]
  have e48 : q + signExtend12 (48 : BitVec 12) = q + 48 := by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide]
  have e40 : q + signExtend12 (40 : BitVec 12) = q + 40 := by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide]
  have e32 : q + signExtend12 (32 : BitVec 12) = q + 32 := by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide]
  have e24 : q + signExtend12 (24 : BitVec 12) = q + 24 := by
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]
  have e16 : q + signExtend12 (16 : BitVec 12) = q + 16 := by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
  have e8 : q + signExtend12 (8 : BitVec 12) = q + 8 := by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
  have e0 : q + signExtend12 (0 : BitVec 12) = q := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have h107 := ld_spec_gen_within .x22 .x2 q v22 s6In (56 : BitVec 12) (L + 428) (by decide)
  have h108 := ld_spec_gen_within .x21 .x2 q v21 s5In (48 : BitVec 12) (L + 432) (by decide)
  have h109 := ld_spec_gen_within .x20 .x2 q v20 s4In (40 : BitVec 12) (L + 436) (by decide)
  have h110 := ld_spec_gen_within .x19 .x2 q v19 s3In (32 : BitVec 12) (L + 440) (by decide)
  have h111 := ld_spec_gen_within .x18 .x2 q v18 s2In (24 : BitVec 12) (L + 444) (by decide)
  have h112 := ld_spec_gen_within .x9 .x2 q v9 s1In (16 : BitVec 12) (L + 448) (by decide)
  have h113 := ld_spec_gen_within .x8 .x2 q v8 s0In (8 : BitVec 12) (L + 452) (by decide)
  have h114 := ld_spec_gen_within .x1 .x2 q v1 raIn (0 : BitVec 12) (L + 456) (by decide)
  have h115 := addi_spec_gen_same_within .x2 q (96 : BitVec 12) (L + 460) (by decide)
  have h116 := jalr_x0_spec_gen_within .x1 raIn (0 : BitVec 12) (L + 464)
  rw [e56] at h107
  rw [e48] at h108
  rw [e40] at h109
  rw [e32] at h110
  rw [e24] at h111
  rw [e16] at h112
  rw [e8] at h113
  rw [e0] at h114
  rw [show q + signExtend12 (96 : BitVec 12) = q + 96 from by
        rw [show signExtend12 (96 : BitVec 12) = (96 : Word) from by decide]] at h115
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show raIn + (0 : Word) = raIn from by bv_omega] at h116
  runBlock h107 h108 h109 h110 h111 h112 h113 h114 h115 h116

/-- **The failure exit** (`+424 .. +464`, prog idx 106..116): `li a0,1` then the
    shared epilogue.

    ⭐ This is the target of **ten** distinct branches — `+60`, `+80`, `+104`,
    `+128` (the four status/arity tests) and `+324`, `+336`, `+348`, `+360`,
    `+380`, `+404` (the six in-loop rejections).  All ten reach exactly this
    triple; the routine has one failure path, not ten. -/
theorem fail_exit_spec_within (q raIn s0In s1In s2In s3In s4In s5In s6In : Word)
    (v1 v8 v9 v18 v19 v20 v21 v22 : Word) :
    cpsTripleWithin 11 (L + 424) (raIn &&& ~~~1) arityCode
      (regOwn .x10 **
        epiPre q raIn s0In s1In s2In s3In s4In s5In s6In v1 v8 v9 v18 v19 v20 v21 v22)
      ((.x10 ↦ᵣ (1 : Word)) ** epiPost q raIn s0In s1In s2In s3In s4In s5In s6In) := by
  have hepi := cpsTripleWithin_frameL ((.x10 ↦ᵣ (1 : Word))) (by pcf)
    (epilogue_spec_within q raIn s0In s1In s2In s3In s4In s5In s6In
      v1 v8 v9 v18 v19 v20 v21 v22)
  have h106 := cpsTripleWithin_frameR
    (epiPre q raIn s0In s1In s2In s3In s4In s5In s6In v1 v8 v9 v18 v19 v20 v21 v22) (by pcf)
    (cpsTripleWithin_extend_code
      (arity_sub_at 106 (by norm_num) (L + 424) (.LI .x10 (1 : Word)) (by rfl) (by rfl))
      (li_spec_gen_own_within .x10 (1 : Word) (L + 424) (by decide)))
  rw [show (L + 424 : Word) + 4 = L + 428 from by bv_omega] at h106
  exact cpsTripleWithin_mono_nSteps (by omega) (cpsTripleWithin_seq_same_cr h106 hepi)

/-- **The success exit** (`+416 .. +464`, prog idx 104..116): `li a0,0`, jump
    over the failure stub, then the SAME shared epilogue.

    Reached by the single branch at `+112` (the loop guard `beq s5,s4`). -/
theorem ok_exit_spec_within (q raIn s0In s1In s2In s3In s4In s5In s6In : Word)
    (v1 v8 v9 v18 v19 v20 v21 v22 : Word) :
    cpsTripleWithin 12 (L + 416) (raIn &&& ~~~1) arityCode
      (regOwn .x10 **
        epiPre q raIn s0In s1In s2In s3In s4In s5In s6In v1 v8 v9 v18 v19 v20 v21 v22)
      ((.x10 ↦ᵣ (0 : Word)) ** epiPost q raIn s0In s1In s2In s3In s4In s5In s6In) := by
  have hepi := cpsTripleWithin_frameL ((.x10 ↦ᵣ (0 : Word))) (by pcf)
    (epilogue_spec_within q raIn s0In s1In s2In s3In s4In s5In s6In
      v1 v8 v9 v18 v19 v20 v21 v22)
  have h104 := cpsTripleWithin_frameR
    (epiPre q raIn s0In s1In s2In s3In s4In s5In s6In v1 v8 v9 v18 v19 v20 v21 v22) (by pcf)
    (cpsTripleWithin_extend_code
      (arity_sub_at 104 (by norm_num) (L + 416) (.LI .x10 (0 : Word)) (by rfl) (by rfl))
      (li_spec_gen_own_within .x10 (0 : Word) (L + 416) (by decide)))
  rw [show (L + 416 : Word) + 4 = L + 420 from by bv_omega] at h104
  have h105 := jal_x0_spec_gen_within (8 : BitVec 21) (L + 420)
  rw [show (L + 420) + signExtend21 (8 : BitVec 21) = L + 428 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at h105
  have h105' := cpsTripleWithin_frameL
    ((.x10 ↦ᵣ (0 : Word)) **
      epiPre q raIn s0In s1In s2In s3In s4In s5In s6In v1 v8 v9 v18 v19 v20 v21 v22) (by pcf)
    (cpsTripleWithin_extend_code
      (arity_sub_at 105 (by norm_num) (L + 420) (.JAL .x0 (8 : BitVec 21)) (by rfl) (by rfl))
      h105)
  rw [sepConj_emp_right'] at h105'
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr h104 (cpsTripleWithin_seq_same_cr h105' hepi))

/-! ## ⭐ The four length-check arms: ONE lemma, four instantiations.

    `+320`, `+332`, `+344` and `+356` are byte-for-byte the same three
    instructions with a different constant:

    ```
    li   t0, K          -- K = 32, 20, 256, 8
    bne  a2, t0, +424   -- reported content length is not K  ->  FAIL
    j    +408           -- length accepted, continue the loop
    ```

    `len_check_arm_within` is stated over the arm's entry `A`, the constant `K`
    and the two encoded displacements, with the three code lookups as
    hypotheses.  The four instantiations below discharge those lookups as
    kernel-checked `rfl`s — twelve of them — and prove nothing new. -/

/-- A length-check arm: reject unless the walker's reported content length `a2`
    is exactly `K`.  Taken exit is the shared `+424` failure stub; the
    fall-through exit is the loop's `+408` join. -/
theorem len_check_arm_within (A K a2 : Word) (boff : BitVec 13) (joff : BitVec 21)
    (hli : ∀ a' i', CodeReq.singleton A (.LI .x5 K) a' = some i' → arityCode a' = some i')
    (hbne : ∀ a' i',
      CodeReq.singleton (A + 4) (.BNE .x12 .x5 boff) a' = some i' → arityCode a' = some i')
    (hjal : ∀ a' i',
      CodeReq.singleton (A + 8) (.JAL .x0 joff) a' = some i' → arityCode a' = some i')
    (hbt : (A + 4) + signExtend13 boff = L + 424)
    (hjt : (A + 8) + signExtend21 joff = L + 408) :
    cpsBranchWithin 3 A arityCode
      ((.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ K) ** ⌜a2 ≠ K⌝)
      (L + 408) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ K) ** ⌜a2 = K⌝) := by
  have h0 := cpsTripleWithin_frameL ((.x12 ↦ᵣ a2)) (by pcf)
    (cpsTripleWithin_extend_code hli (li_spec_gen_own_within .x5 K A (by decide)))
  have h1 := cpsBranchWithin_extend_code hbne (bne_spec_gen_within .x12 .x5 boff a2 K (A + 4))
  rw [hbt] at h1
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_same_cr h0 h1
  rw [show (A + 4 : Word) + 4 = A + 8 from by bv_omega] at hbr
  have h2 := cpsTripleWithin_extend_code hjal (jal_x0_spec_gen_within joff (A + 8))
  rw [hjt] at h2
  have h2' := cpsTripleWithin_frameL
    ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ K) ** ⌜a2 = K⌝) (by pcf) h2
  rw [sepConj_emp_right'] at h2'
  exact cpsBranchWithin_seq_cpsTripleWithin_same_cr hbr h2' (fun _ hp => hp)

/-- Arm for field indices `{0,1,3,4,5,13,16,19,20,21}` (prog idx 80..82,
    `+320`): a 32-byte content (the hashes, roots, blooms' fixed-width slots). -/
theorem len_arm_32_within (a2 : Word) :
    cpsBranchWithin 3 (L + 320) arityCode
      ((.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (32 : Word)) ** ⌜a2 ≠ (32 : Word)⌝)
      (L + 408) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (32 : Word)) ** ⌜a2 = (32 : Word)⌝) :=
  len_check_arm_within (L + 320) (32 : Word) a2 _ _
    (arity_sub_at 80 (by norm_num) (L + 320) _ (by rfl) (by rfl))
    (arity_sub_at 81 (by norm_num) (L + 320 + 4) _ (by bv_omega) (by rfl))
    (arity_sub_at 82 (by norm_num) (L + 320 + 8) _ (by bv_omega) (by rfl))
    (by decide) (by decide)

/-- Arm for field index `2` (prog idx 83..85, `+332`): a 20-byte content — the
    coinbase address. -/
theorem len_arm_20_within (a2 : Word) :
    cpsBranchWithin 3 (L + 332) arityCode
      ((.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (20 : Word)) ** ⌜a2 ≠ (20 : Word)⌝)
      (L + 408) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (20 : Word)) ** ⌜a2 = (20 : Word)⌝) :=
  len_check_arm_within (L + 332) (20 : Word) a2 _ _
    (arity_sub_at 83 (by norm_num) (L + 332) _ (by rfl) (by rfl))
    (arity_sub_at 84 (by norm_num) (L + 332 + 4) _ (by bv_omega) (by rfl))
    (arity_sub_at 85 (by norm_num) (L + 332 + 8) _ (by bv_omega) (by rfl))
    (by decide) (by decide)

/-- Arm for field index `6` (prog idx 86..88, `+344`): a 256-byte content — the
    logs bloom. -/
theorem len_arm_256_within (a2 : Word) :
    cpsBranchWithin 3 (L + 344) arityCode
      ((.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (256 : Word)) ** ⌜a2 ≠ (256 : Word)⌝)
      (L + 408) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (256 : Word)) ** ⌜a2 = (256 : Word)⌝) :=
  len_check_arm_within (L + 344) (256 : Word) a2 _ _
    (arity_sub_at 86 (by norm_num) (L + 344) _ (by rfl) (by rfl))
    (arity_sub_at 87 (by norm_num) (L + 344 + 4) _ (by bv_omega) (by rfl))
    (arity_sub_at 88 (by norm_num) (L + 344 + 8) _ (by bv_omega) (by rfl))
    (by decide) (by decide)

/-- Arm for field index `14` (prog idx 89..91, `+356`): an 8-byte content — the
    extra-data-adjacent fixed-width slot. -/
theorem len_arm_8_within (a2 : Word) :
    cpsBranchWithin 3 (L + 356) arityCode
      ((.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (8 : Word)) ** ⌜a2 ≠ (8 : Word)⌝)
      (L + 408) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (8 : Word)) ** ⌜a2 = (8 : Word)⌝) :=
  len_check_arm_within (L + 356) (8 : Word) a2 _ _
    (arity_sub_at 89 (by norm_num) (L + 356) _ (by rfl) (by rfl))
    (arity_sub_at 90 (by norm_num) (L + 356 + 4) _ (by bv_omega) (by rfl))
    (arity_sub_at 91 (by norm_num) (L + 356 + 8) _ (by bv_omega) (by rfl))
    (by decide) (by decide)

/-! ## ⭐ The 22-probe dispatch: ONE probe lemma, twenty-two instantiations.

    `+140 .. +312` is twenty-two copies of

    ```
    li   t0, K
    beq  s5, t0, T
    ```

    differing only in `(K, T)`, followed by `+316 j +408` for the field indices
    no probe names.  `dispatch_probe_within` is the single two-instruction
    lemma; `dispatch_step` chains one probe onto the rest.

    ⭐ **No 23-way case split anywhere.**  `dispatchFrom` makes the dispatch
    target a *function* of `s5`, so `dispatch_spec_within` is an ordinary
    single-exit `cpsTripleWithin` whose exit PC happens to be computed.  The
    only case analysis is the two-way `by_cases` inside `dispatch_step`, which
    is proved once. -/

/-- The dispatch table, in program order: `(field index, branch target)`.
    All 22 constants are distinct, so first-match-wins is not load-bearing —
    but `dispatchFrom` is defined in program order anyway, to match the code. -/
def probeList : List (Word × Word) :=
  [ ((0 : Word), L + 320),
   ((1 : Word), L + 320),
   ((3 : Word), L + 320),
   ((4 : Word), L + 320),
   ((5 : Word), L + 320),
   ((13 : Word), L + 320),
   ((16 : Word), L + 320),
   ((19 : Word), L + 320),
   ((20 : Word), L + 320),
   ((21 : Word), L + 320),
   ((2 : Word), L + 332),
   ((6 : Word), L + 344),
   ((14 : Word), L + 356),
   ((11 : Word), L + 368),
   ((17 : Word), L + 368),
   ((18 : Word), L + 368),
   ((22 : Word), L + 368),
   ((7 : Word), L + 368),
   ((8 : Word), L + 368),
   ((9 : Word), L + 368),
   ((10 : Word), L + 368),
   ((15 : Word), L + 388) ]

/-- The dispatch target as a function of `s5`: the first probe whose constant
    matches, or the `+408` loop join if none does.  Note that field index `12`
    is named by no probe, and neither is any index `≥ 23`: both fall through
    unchecked, which is exactly what `+316` encodes. -/
def dispatchFrom : List (Word × Word) → Word → Word
  | [], _ => L + 408
  | (k, t) :: rest, i => if i = k then t else dispatchFrom rest i

/-- Exit PC of the dispatch block, as a computed function of the loop index. -/
def dispatchTarget (i : Word) : Word := dispatchFrom probeList i

/-- **One dispatch probe** (`li t0,K` ⨾ `beq s5,t0,T`), the lemma all 22 uses
    share.  `x5` is returned merely OWNED on both arms, so probes chain. -/
theorem dispatch_probe_within (A T K i : Word) (boff : BitVec 13)
    (hli : ∀ a' i', CodeReq.singleton A (.LI .x5 K) a' = some i' → arityCode a' = some i')
    (hbeq : ∀ a' i',
      CodeReq.singleton (A + 4) (.BEQ .x21 .x5 boff) a' = some i' → arityCode a' = some i')
    (ht : (A + 4) + signExtend13 boff = T) :
    cpsBranchWithin 2 A arityCode
      ((.x21 ↦ᵣ i) ** regOwn .x5)
      T ((.x21 ↦ᵣ i) ** regOwn .x5 ** ⌜i = K⌝)
      (A + 8) ((.x21 ↦ᵣ i) ** regOwn .x5 ** ⌜i ≠ K⌝) := by
  have h0 := cpsTripleWithin_frameL ((.x21 ↦ᵣ i)) (by pcf)
    (cpsTripleWithin_extend_code hli (li_spec_gen_own_within .x5 K A (by decide)))
  have h1 := cpsBranchWithin_extend_code hbeq (beq_spec_gen_within .x21 .x5 boff i K (A + 4))
  rw [ht] at h1
  have hbr := cpsTripleWithin_seq_cpsBranchWithin_same_cr h0 h1
  rw [show (A + 4 : Word) + 4 = A + 8 from by bv_omega] at hbr
  exact cpsBranchWithin_weaken (fun _ hp => hp)
    (sepConj_mono_right (sepConj_mono (regIs_implies_regOwn .x5) (fun _ hp => hp)))
    (sepConj_mono_right (sepConj_mono (regIs_implies_regOwn .x5) (fun _ hp => hp)))
    hbr

/-- Chain one probe onto the rest of the dispatch.  The `by_cases` on `i = K` is
    the ONLY case analysis in the whole dispatch, and it is proved here once:
    on each side the opposite arm of the branch is refuted by the pure fact the
    `beq` spec attaches, via `cpsBranchWithin_{taken,ntaken}StripPure2`. -/
theorem dispatch_step (A A' T K i : Word) (rest : List (Word × Word)) (m : Nat)
    (boff : BitVec 13)
    (hli : ∀ a' i', CodeReq.singleton A (.LI .x5 K) a' = some i' → arityCode a' = some i')
    (hbeq : ∀ a' i',
      CodeReq.singleton (A + 4) (.BEQ .x21 .x5 boff) a' = some i' → arityCode a' = some i')
    (ht : (A + 4) + signExtend13 boff = T) (hA' : A + 8 = A')
    (hrest : cpsTripleWithin m A' (dispatchFrom rest i) arityCode
      ((.x21 ↦ᵣ i) ** regOwn .x5) ((.x21 ↦ᵣ i) ** regOwn .x5)) :
    cpsTripleWithin (2 + m) A (dispatchFrom ((K, T) :: rest) i) arityCode
      ((.x21 ↦ᵣ i) ** regOwn .x5) ((.x21 ↦ᵣ i) ** regOwn .x5) := by
  have hprobe := dispatch_probe_within A T K i boff hli hbeq ht
  rw [hA'] at hprobe
  by_cases hik : i = K
  · rw [show dispatchFrom ((K, T) :: rest) i = T from by simp [dispatchFrom, hik]]
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsBranchWithin_takenStripPure2 hprobe (fun _ hq => by
        obtain ⟨_, g2, _, _, _, hr⟩ := hq
        exact ((sepConj_pure_right g2).1 hr).2 hik))
  · rw [show dispatchFrom ((K, T) :: rest) i = dispatchFrom rest i from by
        simp [dispatchFrom, hik]]
    exact cpsTripleWithin_seq_same_cr
      (cpsBranchWithin_ntakenStripPure2 hprobe (fun _ hq => by
        obtain ⟨_, g2, _, _, _, hr⟩ := hq
        exact hik (((sepConj_pure_right g2).1 hr).2)))
      hrest


/-- **The whole dispatch block** (`+140 .. +316`, prog idx 35..79, 45
    instructions): twenty-two probes and the default jump, as a SINGLE-exit
    triple whose exit PC is `dispatchTarget s5`.

    Step bound `45 = 2 * 22 + 1`, one per instruction — the block is
    straight-line in the sense that every path through it executes a prefix of
    the probes and then leaves. -/
theorem dispatch_spec_within (i : Word) :
    cpsTripleWithin 45 (L + 140) (dispatchTarget i) arityCode
      ((.x21 ↦ᵣ i) ** regOwn .x5) ((.x21 ↦ᵣ i) ** regOwn .x5) := by
  unfold dispatchTarget probeList
  have c22 : cpsTripleWithin 1 (L + 316) (dispatchFrom [] i) arityCode
      ((.x21 ↦ᵣ i) ** regOwn .x5) ((.x21 ↦ᵣ i) ** regOwn .x5) := by
    show cpsTripleWithin 1 (L + 316) (L + 408) arityCode _ _
    have hj := cpsTripleWithin_extend_code
      (arity_sub_at 79 (by norm_num) (L + 316) (.JAL .x0 (92 : BitVec 21)) (by rfl) (by decide))
      (jal_x0_spec_gen_within (92 : BitVec 21) (L + 316))
    rw [show (L + 316 : Word) + signExtend21 (92 : BitVec 21) = L + 408 from by
          rw [show signExtend21 (92 : BitVec 21) = (92 : Word) from by decide]; bv_omega] at hj
    have hj' := cpsTripleWithin_frameL ((.x21 ↦ᵣ i) ** regOwn .x5) (by pcf) hj
    rw [sepConj_emp_right'] at hj'
    exact hj'
  have c21 := dispatch_step (L + 308) (L + 316) (L + 388) (15 : Word) i _ _ _
    (arity_sub_at 77 (by norm_num) (L + 308) _ (by rfl) (by rfl))
    (arity_sub_at 78 (by norm_num) (L + 308 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c22
  have c20 := dispatch_step (L + 300) (L + 308) (L + 368) (10 : Word) i _ _ _
    (arity_sub_at 75 (by norm_num) (L + 300) _ (by rfl) (by rfl))
    (arity_sub_at 76 (by norm_num) (L + 300 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c21
  have c19 := dispatch_step (L + 292) (L + 300) (L + 368) (9 : Word) i _ _ _
    (arity_sub_at 73 (by norm_num) (L + 292) _ (by rfl) (by rfl))
    (arity_sub_at 74 (by norm_num) (L + 292 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c20
  have c18 := dispatch_step (L + 284) (L + 292) (L + 368) (8 : Word) i _ _ _
    (arity_sub_at 71 (by norm_num) (L + 284) _ (by rfl) (by rfl))
    (arity_sub_at 72 (by norm_num) (L + 284 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c19
  have c17 := dispatch_step (L + 276) (L + 284) (L + 368) (7 : Word) i _ _ _
    (arity_sub_at 69 (by norm_num) (L + 276) _ (by rfl) (by rfl))
    (arity_sub_at 70 (by norm_num) (L + 276 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c18
  have c16 := dispatch_step (L + 268) (L + 276) (L + 368) (22 : Word) i _ _ _
    (arity_sub_at 67 (by norm_num) (L + 268) _ (by rfl) (by rfl))
    (arity_sub_at 68 (by norm_num) (L + 268 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c17
  have c15 := dispatch_step (L + 260) (L + 268) (L + 368) (18 : Word) i _ _ _
    (arity_sub_at 65 (by norm_num) (L + 260) _ (by rfl) (by rfl))
    (arity_sub_at 66 (by norm_num) (L + 260 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c16
  have c14 := dispatch_step (L + 252) (L + 260) (L + 368) (17 : Word) i _ _ _
    (arity_sub_at 63 (by norm_num) (L + 252) _ (by rfl) (by rfl))
    (arity_sub_at 64 (by norm_num) (L + 252 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c15
  have c13 := dispatch_step (L + 244) (L + 252) (L + 368) (11 : Word) i _ _ _
    (arity_sub_at 61 (by norm_num) (L + 244) _ (by rfl) (by rfl))
    (arity_sub_at 62 (by norm_num) (L + 244 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c14
  have c12 := dispatch_step (L + 236) (L + 244) (L + 356) (14 : Word) i _ _ _
    (arity_sub_at 59 (by norm_num) (L + 236) _ (by rfl) (by rfl))
    (arity_sub_at 60 (by norm_num) (L + 236 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c13
  have c11 := dispatch_step (L + 228) (L + 236) (L + 344) (6 : Word) i _ _ _
    (arity_sub_at 57 (by norm_num) (L + 228) _ (by rfl) (by rfl))
    (arity_sub_at 58 (by norm_num) (L + 228 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c12
  have c10 := dispatch_step (L + 220) (L + 228) (L + 332) (2 : Word) i _ _ _
    (arity_sub_at 55 (by norm_num) (L + 220) _ (by rfl) (by rfl))
    (arity_sub_at 56 (by norm_num) (L + 220 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c11
  have c9 := dispatch_step (L + 212) (L + 220) (L + 320) (21 : Word) i _ _ _
    (arity_sub_at 53 (by norm_num) (L + 212) _ (by rfl) (by rfl))
    (arity_sub_at 54 (by norm_num) (L + 212 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c10
  have c8 := dispatch_step (L + 204) (L + 212) (L + 320) (20 : Word) i _ _ _
    (arity_sub_at 51 (by norm_num) (L + 204) _ (by rfl) (by rfl))
    (arity_sub_at 52 (by norm_num) (L + 204 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c9
  have c7 := dispatch_step (L + 196) (L + 204) (L + 320) (19 : Word) i _ _ _
    (arity_sub_at 49 (by norm_num) (L + 196) _ (by rfl) (by rfl))
    (arity_sub_at 50 (by norm_num) (L + 196 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c8
  have c6 := dispatch_step (L + 188) (L + 196) (L + 320) (16 : Word) i _ _ _
    (arity_sub_at 47 (by norm_num) (L + 188) _ (by rfl) (by rfl))
    (arity_sub_at 48 (by norm_num) (L + 188 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c7
  have c5 := dispatch_step (L + 180) (L + 188) (L + 320) (13 : Word) i _ _ _
    (arity_sub_at 45 (by norm_num) (L + 180) _ (by rfl) (by rfl))
    (arity_sub_at 46 (by norm_num) (L + 180 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c6
  have c4 := dispatch_step (L + 172) (L + 180) (L + 320) (5 : Word) i _ _ _
    (arity_sub_at 43 (by norm_num) (L + 172) _ (by rfl) (by rfl))
    (arity_sub_at 44 (by norm_num) (L + 172 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c5
  have c3 := dispatch_step (L + 164) (L + 172) (L + 320) (4 : Word) i _ _ _
    (arity_sub_at 41 (by norm_num) (L + 164) _ (by rfl) (by rfl))
    (arity_sub_at 42 (by norm_num) (L + 164 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c4
  have c2 := dispatch_step (L + 156) (L + 164) (L + 320) (3 : Word) i _ _ _
    (arity_sub_at 39 (by norm_num) (L + 156) _ (by rfl) (by rfl))
    (arity_sub_at 40 (by norm_num) (L + 156 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c3
  have c1 := dispatch_step (L + 148) (L + 156) (L + 320) (1 : Word) i _ _ _
    (arity_sub_at 37 (by norm_num) (L + 148) _ (by rfl) (by rfl))
    (arity_sub_at 38 (by norm_num) (L + 148 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c2
  have c0 := dispatch_step (L + 140) (L + 148) (L + 320) (0 : Word) i _ _ _
    (arity_sub_at 35 (by norm_num) (L + 140) _ (by rfl) (by rfl))
    (arity_sub_at 36 (by norm_num) (L + 140 + 4) _ (by bv_omega) (by rfl))
    (by decide) (by bv_omega) c1
  exact cpsTripleWithin_mono_nSteps (by norm_num) c0

/-! ## ⭐ The arity check itself.

    The routine is named for `+92 .. +104`: the RLP item count `s4` must be
    exactly `21` (a pre-Cancun header) or `23` (with the two blob fields).
    Anything else takes the shared `+424` failure stub. -/

/-- **The arity gate** (`+92 .. +104`, prog idx 23..26): `s4 ∈ {21, 23}`, else
    fail.  Both accepting branches converge on `+108` (`li s5,0`, the loop
    entry) and the single rejecting branch on the shared `+424` stub.

    The rejecting post records `n ≠ 23` only.  `n ≠ 21` is also true there — it
    is what the first `beq` fell through on — but the failure stub reads
    neither, so it is not carried. -/
theorem arity_gate_within (n : Word) :
    cpsBranchWithin 4 (L + 92) arityCode
      ((.x20 ↦ᵣ n) ** regOwn .x5)
      (L + 108) ((.x20 ↦ᵣ n) ** regOwn .x5 ** ⌜n = (21 : Word) ∨ n = (23 : Word)⌝)
      (L + 424) ((.x20 ↦ᵣ n) ** regOwn .x5 ** ⌜n ≠ (23 : Word)⌝) := by
  have hown : ∀ (v : Word) (p : Prop),
      ∀ h, ((.x20 ↦ᵣ n) ** (.x5 ↦ᵣ v) ** ⌜p⌝) h →
        ((.x20 ↦ᵣ n) ** regOwn .x5 ** ⌜p⌝) h :=
    fun _ _ => sepConj_mono_right (sepConj_mono (regIs_implies_regOwn .x5) (fun _ hp => hp))
  -- idx 23..24: `li t0,21` ⨾ `beq s4,t0,+108`.
  have a0 := cpsTripleWithin_frameL ((.x20 ↦ᵣ n)) (by pcf)
    (cpsTripleWithin_extend_code
      (arity_sub_at 23 (by norm_num) (L + 92) (.LI .x5 (21 : Word)) (by rfl) (by rfl))
      (li_spec_gen_own_within .x5 (21 : Word) (L + 92) (by decide)))
  have a1 := cpsBranchWithin_extend_code
    (arity_sub_at 24 (by norm_num) (L + 92 + 4) _ (by bv_omega) (by rfl))
    (beq_spec_gen_within .x20 .x5 (12 : BitVec 13) n (21 : Word) (L + 92 + 4))
  rw [show (L + 92 + 4 : Word) + signExtend13 (12 : BitVec 13) = L + 108 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]
        bv_omega] at a1
  have b1 := cpsBranchWithin_weaken (fun _ hp => hp)
    (hown (21 : Word) _) (hown (21 : Word) _)
    (cpsTripleWithin_seq_cpsBranchWithin_same_cr a0 a1)
  rw [show (L + 92 : Word) + 4 + 4 = L + 100 from by bv_omega] at b1
  -- idx 25..26: `li t0,23` ⨾ `bne s4,t0,+424`, swapped so its ACCEPTING exit
  -- (`n = 23`, fall-through to `+108`) becomes the shared target.
  have a2 := cpsTripleWithin_frameL ((.x20 ↦ᵣ n)) (by pcf)
    (cpsTripleWithin_extend_code
      (arity_sub_at 25 (by norm_num) (L + 100) (.LI .x5 (23 : Word)) (by rfl) (by rfl))
      (li_spec_gen_own_within .x5 (23 : Word) (L + 100) (by decide)))
  have a3 := cpsBranchWithin_extend_code
    (arity_sub_at 26 (by norm_num) (L + 100 + 4) _ (by bv_omega) (by rfl))
    (bne_spec_gen_within .x20 .x5 _ n (23 : Word) (L + 100 + 4))
  rw [show (L + 100 + 4 : Word) + signExtend13
      (brOff (GuestAddrs.header_extended_decode_arity_check + 424)
             (GuestAddrs.header_extended_decode_arity_check + 104)) = L + 424 from by
    decide] at a3
  have b2 := cpsBranchWithin_weaken (fun _ hp => hp)
    (hown (23 : Word) _) (hown (23 : Word) _)
    (cpsTripleWithin_seq_cpsBranchWithin_same_cr a2 a3)
  rw [show (L + 100 : Word) + 4 + 4 = L + 108 from by bv_omega] at b2
  -- The first branch's fall-through carries `⌜n ≠ 21⌝`, which the second block
  -- does not need; drop it so the two pre-conditions meet.
  have b2' := cpsBranchWithin_weaken
    (P' := (.x20 ↦ᵣ n) ** regOwn .x5 ** ⌜n ≠ (21 : Word)⌝)
    (sepConj_mono_right (fun h hq => ((sepConj_pure_right h).1 hq).1))
    (fun _ hp => hp) (fun _ hp => hp) (cpsBranchWithin_swap b2)
  exact cpsBranchWithin_seq_cpsBranchWithin_same_cr b1 b2'
    (sepConj_mono_right (sepConj_mono_right (fun _ hp => ⟨hp.1, Or.inl hp.2⟩)))
    (sepConj_mono_right (sepConj_mono_right (fun _ hp => ⟨hp.1, Or.inr hp.2⟩)))

/-! ## The loop's control skeleton: guard, back edge, measure.

    These three settle the TERMINATION half of the loop.  What they do NOT
    settle is the invariant's memory component — see the module docstring for
    the walk-post ⇒ walk-pre blocker, which is why there is no loop rule applied
    here and no whole-routine triple. -/

/-- **The loop guard** (`+112`, prog idx 28): `beq s5,s4` — leave through the
    success exit when the index has reached the item count, otherwise enter the
    body at `+116`. -/
theorem loop_guard_within (i n : Word) :
    cpsBranchWithin 1 (L + 112) arityCode
      ((.x21 ↦ᵣ i) ** (.x20 ↦ᵣ n))
      (L + 416) ((.x21 ↦ᵣ i) ** (.x20 ↦ᵣ n) ** ⌜i = n⌝)
      (L + 116) ((.x21 ↦ᵣ i) ** (.x20 ↦ᵣ n) ** ⌜i ≠ n⌝) := by
  have h := cpsBranchWithin_extend_code
    (arity_sub_at 28 (by norm_num) (L + 112) _ (by rfl) (by rfl))
    (beq_spec_gen_within .x21 .x20 _ i n (L + 112))
  rwa [show (L + 112 : Word) + signExtend13
      (brOff (GuestAddrs.header_extended_decode_arity_check + 416)
             (GuestAddrs.header_extended_decode_arity_check + 112)) = L + 416 from by
    decide] at h

/-- **The back edge** (`+408 .. +412`, prog idx 102..103), the routine's ONLY
    backward transfer: `addi s5,s5,1` then `j +112`.  This is the whole of the
    loop's update — nothing else in the body writes `s5`. -/
theorem loop_backedge_within (i : Word) :
    cpsTripleWithin 2 (L + 408) (L + 112) arityCode
      (.x21 ↦ᵣ i) (.x21 ↦ᵣ (i + 1)) := by
  have h0 := cpsTripleWithin_extend_code
    (arity_sub_at 102 (by norm_num) (L + 408) (.ADDI .x21 .x21 (1 : BitVec 12))
      (by rfl) (by rfl))
    (addi_spec_gen_same_within .x21 i (1 : BitVec 12) (L + 408) (by decide))
  rw [show i + signExtend12 (1 : BitVec 12) = i + 1 from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]] at h0
  have h1 := cpsTripleWithin_extend_code
    (arity_sub_at 103 (by norm_num) (L + 412) (.JAL .x0 (-300 : BitVec 21))
      (by rfl) (by decide))
    (jal_x0_spec_gen_within (-300 : BitVec 21) (L + 412))
  rw [show (L + 412 : Word) + signExtend21 (-300 : BitVec 21) = L + 112 from by
        rw [show signExtend21 (-300 : BitVec 21) = (-300 : Word) from by decide]
        bv_omega] at h1
  have h1' := cpsTripleWithin_frameL ((.x21 ↦ᵣ (i + 1))) (by pcf) h1
  rw [sepConj_emp_right'] at h1'
  rw [show (L + 408 : Word) + 4 = L + 412 from by bv_omega] at h0
  exact cpsTripleWithin_seq_same_cr h0 h1'

/-- **The measure.**  `(n - i : Nat)` on `(s4, s5)` strictly decreases across the
    back edge, given the loop guard's `i ≠ n` and the entry fact `i ≤ n`
    (`s5` starts at `0` at `+108` and only ever grows by one).  Note the
    `toNat` step needs no extra no-wrap hypothesis: `i < n ≤ 2^64 - 1` already
    forbids `i + 1` from wrapping. -/
theorem loop_measure_decreases (i n : Word) (hlt : i.toNat < n.toNat) :
    n.toNat - (i + 1).toNat < n.toNat - i.toNat := by
  have hn : n.toNat < 2 ^ 64 := n.isLt
  have h1 : (i + 1).toNat = i.toNat + 1 := by
    have : ((1 : Word)).toNat = 1 := by decide
    rw [BitVec.toNat_add, this]
    omega
  omega

/-! ## ⭐ Dispatch ⨾ arm: the fan-in actually connects.

    `dispatch_spec_within` ends at `dispatchTarget s5` and the four arms start
    at `+320/+332/+344/+356`; `dispatch_then_arm_within` is the composition, so
    the two halves are shown to meet rather than merely to exist side by side.
    It covers `+140 .. +328` (prog idx 35..82) in one `cpsBranchWithin`, and its
    taken exit is the shared `+424` failure stub — the same one
    `fail_exit_spec_within` closes. -/

/-- Run the dispatch and then whichever length arm it selects: from `+140`, in
    48 steps, to either the shared `+424` failure stub (the reported content
    length is not `K`) or the `+408` loop join (it is). -/
theorem dispatch_then_arm_within (i K A a2 : Word)
    (hd : dispatchTarget i = A)
    (harm : cpsBranchWithin 3 A arityCode
      ((.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ K) ** ⌜a2 ≠ K⌝)
      (L + 408) ((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ K) ** ⌜a2 = K⌝)) :
    cpsBranchWithin 48 (L + 140) arityCode
      ((.x21 ↦ᵣ i) ** (.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424) (((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ K) ** ⌜a2 ≠ K⌝) ** (.x21 ↦ᵣ i))
      (L + 408) (((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ K) ** ⌜a2 = K⌝) ** (.x21 ↦ᵣ i)) := by
  have hdisp := dispatch_spec_within i
  rw [hd] at hdisp
  have hdisp' := cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR ((.x12 ↦ᵣ a2)) (by pcf) hdisp)
    (P' := (.x21 ↦ᵣ i) ** (.x12 ↦ᵣ a2) ** regOwn .x5)
    (Q' := ((.x12 ↦ᵣ a2) ** regOwn .x5) ** (.x21 ↦ᵣ i))
  have hc := cpsTripleWithin_seq_cpsBranchWithin_same_cr hdisp'
    (cpsBranchWithin_frameR ((.x21 ↦ᵣ i)) (by pcf) harm)
  exact cpsBranchWithin_mono_nSteps (by norm_num) hc

/-- Closed composition at field index `6`: `+140` runs all twelve probes up to
    the `6` probe, lands on `+344`, and rejects unless the logs bloom is exactly
    256 bytes. -/
theorem dispatch_then_arm_6 (a2 : Word) :
    cpsBranchWithin 48 (L + 140) arityCode
      ((.x21 ↦ᵣ (6 : Word)) ** (.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424)
        (((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (256 : Word)) ** ⌜a2 ≠ (256 : Word)⌝) **
          (.x21 ↦ᵣ (6 : Word)))
      (L + 408)
        (((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (256 : Word)) ** ⌜a2 = (256 : Word)⌝) **
          (.x21 ↦ᵣ (6 : Word))) :=
  dispatch_then_arm_within (6 : Word) (256 : Word) (L + 344) a2 (by decide)
    (len_arm_256_within a2)

/-- Closed composition at field index `0` (`parent_hash`): the 32-byte arm. -/
theorem dispatch_then_arm_0 (a2 : Word) :
    cpsBranchWithin 48 (L + 140) arityCode
      ((.x21 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ a2) ** regOwn .x5)
      (L + 424)
        (((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (32 : Word)) ** ⌜a2 ≠ (32 : Word)⌝) **
          (.x21 ↦ᵣ (0 : Word)))
      (L + 408)
        (((.x12 ↦ᵣ a2) ** (.x5 ↦ᵣ (32 : Word)) ** ⌜a2 = (32 : Word)⌝) **
          (.x21 ↦ᵣ (0 : Word))) :=
  dispatch_then_arm_within (0 : Word) (32 : Word) (L + 320) a2 (by decide)
    (len_arm_32_within a2)

/-! ## Non-vacuity.

    Discipline (#12799): a satisfiable instance AND a negative control in which
    the same hypotheses are provably FALSE.  Both are witnessed by abbrevs in
    `Routines.lean`, not merely named in a `notes :=` string. -/

/-- The dispatch really dispatches: three distinct field indices land on three
    distinct targets, and index `12` — named by no probe — lands on the default
    `+408` join.  Without this, `dispatch_spec_within` could be read as a claim
    about a constant function. -/
theorem dispatchTarget_values :
    dispatchTarget (6 : Word) = L + 344 ∧
    dispatchTarget (2 : Word) = L + 332 ∧
    dispatchTarget (15 : Word) = L + 388 ∧
    dispatchTarget (0 : Word) = L + 320 ∧
    dispatchTarget (12 : Word) = L + 408 ∧
    dispatchTarget (99 : Word) = L + 408 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Closed instance of the dispatch at field index `6` (the logs bloom): a
    hypothesis-free 45-step triple from `+140` to the concrete address `+344`,
    the entry of the 256-byte length arm. -/
theorem dispatch_instance_6 :
    cpsTripleWithin 45 (L + 140) (L + 344) arityCode
      ((.x21 ↦ᵣ (6 : Word)) ** regOwn .x5) ((.x21 ↦ᵣ (6 : Word)) ** regOwn .x5) := by
  have h := dispatch_spec_within (6 : Word)
  rwa [show dispatchTarget (6 : Word) = L + 344 from by decide] at h

/-- Closed instance at field index `12`, the ONE index in `0..22` that no probe
    names: the dispatch runs all 22 probes and leaves through the default jump.
    This is the longest path through the block, so it also witnesses that the
    45-step bound is reached and not merely an over-estimate. -/
theorem dispatch_instance_12 :
    cpsTripleWithin 45 (L + 140) (L + 408) arityCode
      ((.x21 ↦ᵣ (12 : Word)) ** regOwn .x5) ((.x21 ↦ᵣ (12 : Word)) ** regOwn .x5) := by
  have h := dispatch_spec_within (12 : Word)
  rwa [show dispatchTarget (12 : Word) = L + 408 from by decide] at h

/-- Closed instance of the shared failure exit at a concrete frame: `a0 := 1`,
    every callee-saved register reloaded, `sp` back up by 96, `ret` to `raIn`. -/
theorem fail_exit_instance :
    cpsTripleWithin 11 (L + 424) ((0xa0000000 : Word) &&& ~~~1) arityCode
      (regOwn .x10 **
        epiPre (0xa0000100 : Word) (0xa0000000 : Word) 1 2 3 4 5 6 7 0 0 0 0 0 0 0 0)
      ((.x10 ↦ᵣ (1 : Word)) **
        epiPost (0xa0000100 : Word) (0xa0000000 : Word) 1 2 3 4 5 6 7) :=
  fail_exit_spec_within (0xa0000100 : Word) (0xa0000000 : Word) 1 2 3 4 5 6 7 0 0 0 0 0 0 0 0

/-- Closed instance of the shared SUCCESS exit at the same frame.  Paired with
    `fail_exit_instance` it witnesses that sharing the epilogue did NOT collapse
    the two exits: same 17 frame arguments, different `a0`. -/
theorem ok_exit_instance :
    cpsTripleWithin 12 (L + 416) ((0xa0000000 : Word) &&& ~~~1) arityCode
      (regOwn .x10 **
        epiPre (0xa0000100 : Word) (0xa0000000 : Word) 1 2 3 4 5 6 7 0 0 0 0 0 0 0 0)
      ((.x10 ↦ᵣ (0 : Word)) **
        epiPost (0xa0000100 : Word) (0xa0000000 : Word) 1 2 3 4 5 6 7) :=
  ok_exit_spec_within (0xa0000100 : Word) (0xa0000000 : Word) 1 2 3 4 5 6 7 0 0 0 0 0 0 0 0

/-- NEGATIVE CONTROL.  Each conjunct is a hypothesis of one of this module's
    parameterised lemmas, instantiated the WRONG way, and refuted — so none of
    them is a tautology that any instantiation would satisfy.

    1. `len_check_arm_within`'s `hbt` at the `+320` arm: the `bne` really
       targets the shared FAILURE stub, never the `+408` loop join.  If this
       were provable the length check would accept every length.
    2. `len_check_arm_within`'s `hli` lookup at `+320` with the NEIGHBOURING
       arm's constant: the four instantiations are not interchangeable.
    3. `dispatch_probe_within`'s `hli` lookup at `+140` with the wrong
       register: the probes read `t0`/`s5`, not `a2`.
    4. `dispatchTarget` at index `12` is NOT the 32-byte arm — the default arm
       is a real, reachable arm and not an artefact of the encoding. -/
theorem arity_premises_refutable :
    ¬ ((L + 320 + 4) + signExtend13
        (brOff (GuestAddrs.header_extended_decode_arity_check + 424)
               (GuestAddrs.header_extended_decode_arity_check + 324)) = L + 408) ∧
    ¬ (arityCode (L + 320) = some (.LI .x5 (20 : Word))) ∧
    ¬ (arityCode (L + 140) = some (.LI .x12 (0 : Word))) ∧
    ¬ (dispatchTarget (12 : Word) = L + 320) := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · rw [arity_at 80 (by norm_num) (L + 320) (by rfl)]; decide
  · rw [arity_at 35 (by norm_num) (L + 140) (by rfl)]; decide

end EvmAsm.Codegen.HeaderArityCheckTie
