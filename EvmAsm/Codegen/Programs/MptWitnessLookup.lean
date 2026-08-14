/-
  EvmAsm.Codegen.Programs.MptWitnessLookup

  Witness lookup helpers used by MPT and state/code proof programs.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.MptWitnessIndex
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## witness_lookup_by_hash -- PR-K19 (linear-scan flavour)

    Find the entry in an SSZ list section whose keccak256 digest
    matches a caller-supplied target hash. Returns the matched
    entry's (offset, length) within the section, or status=1 on
    miss.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.state /
                    witness.codes shape)
      a1 (input)  : section_len (0 ⇒ guaranteed miss)
      a2 (input)  : 32-byte target hash ptr
      a3 (input)  : u64 out ptr (matched entry's byte offset
                    within the section; meaningful only on hit)
      a4 (input)  : u64 out ptr (matched entry's byte length;
                    meaningful only on hit)
      ra (input)  : return
      a0 (output) : 0 on hit, 1 on miss

    Walks every element computing `keccak256(element_bytes)`
    until either a match is found or the list is exhausted.

    Large stateless-verdict runs build a sorted NodeDb index once via
    `witness_index_build`; when the `(section_ptr,len)` matches that index
    this routine uses binary search instead of rescanning. The index is
    deterministic and sorted by the full 32-byte hash, not an
    attacker-shaped hash bucket chain.

    The linear fallback is NOT size-capped: sections without a registered
    index (notably `witness.codes`, which can legitimately exceed 64 KiB --
    e.g. the 72945-byte modified predeploy in EEST
    `system_contract_reaches_gas_limit`) must still resolve correctly. A
    size cap here silently converted such lookups into misses and made the
    code-preimage gate false-reject valid blocks. Repeated lookups against
    a large unindexed section are a cycle-budget concern, not a soundness
    one; bound them at the caller or register an index. -/
def witnessLookupByHash_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .AUIPC .x5 (laHi GuestAddrs.wlh_lookup_calls (GuestAddrs.witness_lookup_by_hash + 56)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_lookup_calls (GuestAddrs.witness_lookup_by_hash + 56)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.widx_enabled (GuestAddrs.witness_lookup_by_hash + 76)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_enabled (GuestAddrs.witness_lookup_by_hash + 76)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.witness_lookup_by_hash + 220) (GuestAddrs.witness_lookup_by_hash + 88)),
    .AUIPC .x5 (laHi GuestAddrs.widx_section_ptr (GuestAddrs.witness_lookup_by_hash + 92)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_section_ptr (GuestAddrs.witness_lookup_by_hash + 92)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BNE .x8 .x5 (brOff (GuestAddrs.witness_lookup_by_hash + 220) (GuestAddrs.witness_lookup_by_hash + 104)),
    .AUIPC .x5 (laHi GuestAddrs.widx_section_len (GuestAddrs.witness_lookup_by_hash + 108)),
    .ADDI .x5 .x5 (laLo GuestAddrs.widx_section_len (GuestAddrs.witness_lookup_by_hash + 108)),
    .LD .x5 .x5 (0 : BitVec 12),
    .BNE .x9 .x5 (brOff (GuestAddrs.witness_lookup_by_hash + 220) (GuestAddrs.witness_lookup_by_hash + 120)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x5 (laHi GuestAddrs.wlh_indexed_calls (GuestAddrs.witness_lookup_by_hash + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_indexed_calls (GuestAddrs.witness_lookup_by_hash + 144)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.witness_lookup_by_hash_indexed (GuestAddrs.witness_lookup_by_hash + 164)),
    .BNE .x10 .x0 (28 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.wlh_indexed_hits (GuestAddrs.witness_lookup_by_hash + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_indexed_hits (GuestAddrs.witness_lookup_by_hash + 172)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_lookup_by_hash + 580) (GuestAddrs.witness_lookup_by_hash + 192)),
    .AUIPC .x5 (laHi GuestAddrs.wlh_indexed_misses (GuestAddrs.witness_lookup_by_hash + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_indexed_misses (GuestAddrs.witness_lookup_by_hash + 196)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_lookup_by_hash + 580) (GuestAddrs.witness_lookup_by_hash + 216)),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_calls (GuestAddrs.witness_lookup_by_hash + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_calls (GuestAddrs.witness_lookup_by_hash + 220)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_last_section_len (GuestAddrs.witness_lookup_by_hash + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_last_section_len (GuestAddrs.witness_lookup_by_hash + 240)),
    .SD .x5 .x9 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_max_section_len (GuestAddrs.witness_lookup_by_hash + 252)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_max_section_len (GuestAddrs.witness_lookup_by_hash + 252)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BGEU .x6 .x9 (8 : BitVec 13),
    .SD .x5 .x9 (0 : BitVec 12),
    .BEQ .x9 .x0 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 272)),
    .LI .x5 (4 : Word),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 280)),
    .LWU .x5 .x8 (0 : BitVec 12),
    .ANDI .x6 .x5 (3 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 292)),
    .BLTU .x9 .x5 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 296)),
    .SRLI .x21 .x5 (2 : BitVec 6),
    .LI .x22 (0 : Word),
    .BEQ .x22 .x21 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 308)),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .BLTU .x9 .x7 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 324)),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x22 (1 : BitVec 12),
    .BEQ .x28 .x21 (28 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .BLTU .x9 .x29 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 352)),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .BLTU .x29 .x10 (brOff (GuestAddrs.witness_lookup_by_hash + 556) (GuestAddrs.witness_lookup_by_hash + 368)),
    .SUB .x11 .x29 .x10,
    .AUIPC .x12 (laHi GuestAddrs.wlh_scratch_hash (GuestAddrs.witness_lookup_by_hash + 376)),
    .ADDI .x12 .x12 (laLo GuestAddrs.wlh_scratch_hash (GuestAddrs.witness_lookup_by_hash + 376)),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_iterations (GuestAddrs.witness_lookup_by_hash + 384)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_iterations (GuestAddrs.witness_lookup_by_hash + 384)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.witness_lookup_by_hash + 404)),
    .AUIPC .x5 (laHi GuestAddrs.wlh_scratch_hash (GuestAddrs.witness_lookup_by_hash + 408)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_scratch_hash (GuestAddrs.witness_lookup_by_hash + 408)),
    .MV .x6 .x18,
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_lookup_by_hash + 548) (GuestAddrs.witness_lookup_by_hash + 428)),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_lookup_by_hash + 548) (GuestAddrs.witness_lookup_by_hash + 440)),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_lookup_by_hash + 548) (GuestAddrs.witness_lookup_by_hash + 452)),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (brOff (GuestAddrs.witness_lookup_by_hash + 548) (GuestAddrs.witness_lookup_by_hash + 464)),
    .SLLI .x5 .x22 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .SD .x19 .x7 (0 : BitVec 12),
    .ADDI .x28 .x22 (1 : BitVec 12),
    .BEQ .x28 .x21 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .SUB .x29 .x29 .x7,
    .JAL .x0 (8 : BitVec 21),
    .SUB .x29 .x9 .x7,
    .SD .x20 .x29 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_hits (GuestAddrs.witness_lookup_by_hash + 520)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_hits (GuestAddrs.witness_lookup_by_hash + 520)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (36 : BitVec 21),
    .ADDI .x22 .x22 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.witness_lookup_by_hash + 308) (GuestAddrs.witness_lookup_by_hash + 552)),
    .AUIPC .x5 (laHi GuestAddrs.wlh_linear_misses (GuestAddrs.witness_lookup_by_hash + 556)),
    .ADDI .x5 .x5 (laLo GuestAddrs.wlh_linear_misses (GuestAddrs.witness_lookup_by_hash + 556)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .SD .x5 .x6 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `witnessLookupByHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def witnessLookupByHash_relocs : RelocTable :=
  [ (14, .la .x5 "wlh_lookup_calls"),
    (19, .la .x5 "widx_enabled"),
    (23, .la .x5 "widx_section_ptr"),
    (27, .la .x5 "widx_section_len"),
    (36, .la .x5 "wlh_indexed_calls"),
    (41, .jal .x1 "witness_lookup_by_hash_indexed"),
    (43, .la .x5 "wlh_indexed_hits"),
    (49, .la .x5 "wlh_indexed_misses"),
    (55, .la .x5 "wlh_linear_calls"),
    (60, .la .x5 "wlh_linear_last_section_len"),
    (63, .la .x5 "wlh_linear_max_section_len"),
    (94, .la .x12 "wlh_scratch_hash"),
    (96, .la .x5 "wlh_linear_iterations"),
    (101, .jal .x1 "zkvm_keccak256"),
    (102, .la .x5 "wlh_scratch_hash"),
    (130, .la .x5 "wlh_linear_hits"),
    (139, .la .x5 "wlh_linear_misses") ]

def witnessLookupByHashEntryFunction : String :=
  "witness_lookup_by_hash:\n" ++ emitProgramR witnessLookupByHash_prog witnessLookupByHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `witnessLookupByHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem witnessLookupByHashEntryFunction_eq_prog :
    witnessLookupByHashEntryFunction = "witness_lookup_by_hash:\n" ++ emitProgramR witnessLookupByHash_prog witnessLookupByHash_relocs := rfl

#guard witnessLookupByHashEntryFunction.startsWith "witness_lookup_by_hash:\n"

/-- Emission bundle: the `witness_lookup_by_hash` routine followed by the
    witness-index helper cluster it dispatches into (`widx_*` plus
    `witness_lookup_by_hash_indexed`). Every consumer -- the guest image via
    `Dispatch.lean` and a dozen `zisk_*` probes -- emits the pair, so the two
    stay concatenated behind this one name.

    ⚠️ The explicit `"\n"` is load-bearing, not cosmetic. Now that
    `witnessLookupByHashEntryFunction` ends in `emitProgramR`, it ends with an
    INSTRUCTION and no trailing newline, whereas the hand-written literal it
    replaced ended with `"  ret\n"`. Nothing in the per-routine conversion gates
    would notice the difference: they assemble one routine at a time and never
    this concatenation. The seam is pinned by the two `#guard`s below instead of
    by prose -- one on each half of the property, so neither side can drift into
    the other's newline. -/
def witnessLookupByHashFunction : String :=
  witnessLookupByHashEntryFunction ++ "\n" ++ witnessIndexFunctions

-- The hazard's premise: `emitProgramR` ends the routine with an instruction,
-- NOT a newline. Were this ever to change, the explicit `"\n"` above would
-- become a spurious blank line rather than the separator it is.
#guard !witnessLookupByHashEntryFunction.endsWith "\n"

-- The seam itself: the cluster's first label occupies its own line, preceded by
-- exactly the blank line the pre-conversion literal produced (its `"  ret\n"`
-- plus `witnessIndexFunctions`' own leading `"\n"`), and occurs exactly once.
-- Drop the separator on either side and this fails; `= 2` is `splitOn`'s
-- encoding of "one occurrence".
#guard (witnessLookupByHashFunction.splitOn "\n\nwidx_record_ptr:\n").length = 2

/-- `zisk_witness_lookup_by_hash`: probe BuildUnit. Reads
    (section_len, target_hash, section_bytes) from host input,
    writes (status, offset, length) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..40 : target_hash (32 bytes)
      bytes 40..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64; 0 hit, 1 miss)
      bytes  8..16 : matched entry offset within section (u64)
      bytes 16..24 : matched entry length (u64) -/
def ziskWitnessLookupByHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a2, a5, 16             # target_hash ptr\n" ++
  "  addi a0, a5, 48             # section ptr\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  # Pre-zero offset/length so a miss surfaces as zeros.\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lwlh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwlh_pdone:"

def ziskWitnessLookupByHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32"


/-- `zisk_witness_lookup_by_hash_indexed`: same probe contract as
    `zisk_witness_lookup_by_hash`, but first builds the sorted witness index and
    then resolves the hash through the indexed path. OUTPUT+24 records the
    index-build status (0 = built, 1 = malformed/cap exceeded). OUTPUT+32
    records the decoded SSZ element count observed by the builder. -/
def ziskWitnessLookupByHashIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld s0, 8(a5)                # section_len\n" ++
  "  addi s1, a5, 16             # target_hash ptr\n" ++
  "  addi s2, a5, 48             # section ptr\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, witness_index_build\n" ++
  "  li t0, 0xa0010018\n" ++
  "  sd a0, 0(t0)                # index-build status at OUTPUT + 24\n" ++
  "  la t0, widx_build_count\n" ++
  "  ld t1, 0(t0)\n" ++
  "  li t0, 0xa0010020\n" ++
  "  sd t1, 0(t0)                # decoded count at OUTPUT + 32\n" ++
  "  bnez a0, .Lwlhi_done\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # lookup status at OUTPUT + 0\n" ++
  ".Lwlhi_done:\n" ++
  "  j .Lwlhi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  ".Lwlhi_pdone:"


end EvmAsm.Codegen
