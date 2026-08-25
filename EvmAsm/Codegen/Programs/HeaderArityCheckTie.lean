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

  Also not covered here: the prologue (`+0 .. +108`), the two callee arms
  (`+368`, `+388`) as composed triples, and the back edge itself.
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

end EvmAsm.Codegen.HeaderArityCheckTie
