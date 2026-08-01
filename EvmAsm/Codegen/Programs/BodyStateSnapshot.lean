/-
  EvmAsm.Codegen.Programs.BodyStateSnapshot

  Source-level emitters for the canonical body-state snapshot slab.  These
  produce the existing straight-line instructions; they are deliberately not
  guest subroutines, so root and child capture retain their exact instruction
  order and rollback timing.

  GH #10619 also gives the slab's SHAPE a name here.  Its per-depth stride was written
  nowhere: all eight consumers open-coded `depth * 104` as a shift-add chain, so the field
  count existed only as the exponents of three `slli`s spread over three files, with the
  total appearing once more as a bare `.zero 106600`.  Adding a field meant editing nine
  sites in a form no search for "104" can find, and getting one wrong shifts every deeper
  frame's snapshot by 8 bytes — a silently wrong rollback, not a build error.
-/

namespace EvmAsm.Codegen

/-- Emit one scalar capture into a field of a body-state snapshot record.
    The caller chooses scratch registers so the generated instruction sequence
    remains identical at each existing capture site. -/
def bodyStateCaptureScalarAsm (sourceLabel destinationReg : String) (destinationOffset : Nat)
    (addressReg valueReg : String) : String :=
  "  la " ++ addressReg ++ ", " ++ sourceLabel ++ "; ld " ++ valueReg ++ ", 0(" ++
    addressReg ++ "); sd " ++ valueReg ++ ", " ++ toString destinationOffset ++
    "(" ++ destinationReg ++ ")\n"

/-- Emit the three live environment cursors into their canonical snapshot
    fields.  `sourceSetup` is either the root environment address materialiser
    or the empty prefix for a frame-local environment register. -/
def bodyStateCaptureCursorsAsm (sourceSetup sourceEnvReg destinationReg valueReg : String) : String :=
  sourceSetup ++ "ld " ++ valueReg ++ ", 448(" ++ sourceEnvReg ++ "); sd " ++ valueReg ++
    ", 40(" ++ destinationReg ++ "); ld " ++ valueReg ++ ", 464(" ++ sourceEnvReg ++
    "); sd " ++ valueReg ++ ", 48(" ++ destinationReg ++ "); ld " ++ valueReg ++
    ", 472(" ++ sourceEnvReg ++ "); sd " ++ valueReg ++ ", 56(" ++ destinationReg ++ ")\n"

/-- Number of 8-byte fields in one depth's `body_state_snapshot_by_depth` record.

    In offset order: `exec_nonstorage_effect_count`, `exec_nonstorage_effect_overflow`,
    `exec_code_effect_count`, `exec_code_effect_next`, `exec_code_effect_overflow`, the
    three `evm_env` cursors, `account_writes_undo_count`, `account_state_pending_count`,
    `account_state_delete_count`, `account_state_overflow`, `create_nonce_undo_count`,
    `storage_writes_undo_count` (GH #10619, at offset 104). -/
def bodyStateSlabFields : Nat := 14

/-- Bytes per depth. -/
def bodyStateSlabStride : Nat := bodyStateSlabFields * 8

/-- Maximum call depth plus one, matching the sibling per-depth arrays
    (`storage_writes_undo_checkpoint`, `create_frame_flag`). -/
def bodyStateSlabDepths : Nat := 1025

/-- Total `.bss` allocation of the slab. -/
def bodyStateSlabBytes : Nat := bodyStateSlabStride * bodyStateSlabDepths

#guard bodyStateSlabStride = 112
#guard bodyStateSlabBytes = 114800

/-- Emit `acc := depth * bodyStateSlabStride` with shifts and adds only.

    `depth` is read repeatedly and never written; `acc` and `tmp` are clobbered, and `tmp`
    must differ from `depth`.  The decomposition walks the stride's set bits from high to
    low, which is exactly what the eight hand-written copies did for 104 (`64 + 32 + 8`), and now renders 112 as `64 + 32 + 16`.

    Returned WITHOUT leading indentation or a trailing newline, so each call site can splice
    it into the single emitted line it already occupies.  That is not cosmetic: emitting it
    as its own line would move `CallFrameDescend`'s `la` from before the chain to after it,
    which changes the instruction ORDER and therefore the linked bytes even though the
    computed value is the same. Measured — that mistake changed both hashes. -/
def bodyStateSlabStrideOps (depth acc tmp : String) : String :=
  let bits := (List.range 16).reverse.filter (fun i => (bodyStateSlabStride >>> i) % 2 == 1)
  match bits with
  | [] => "li " ++ acc ++ ", 0"
  | hi :: rest =>
    "slli " ++ acc ++ ", " ++ depth ++ ", " ++ toString hi ++
      String.join (rest.map (fun i =>
        "; slli " ++ tmp ++ ", " ++ depth ++ ", " ++ toString i ++
        "; add " ++ acc ++ ", " ++ acc ++ ", " ++ tmp))

/-- The same chain as its own indented line, for a site that does not splice. -/
def bodyStateSlabStrideAsm (depth acc tmp : String) : String :=
  "  " ++ bodyStateSlabStrideOps depth acc tmp ++ "\n"

/- Pin the rendering the eight call sites previously wrote by hand, so a stride change
   cannot silently alter the instruction sequence.  A `#guard` takes no docstring. -/
#guard bodyStateSlabStrideOps "t1" "t2" "t3"
  = "slli t2, t1, 6; slli t3, t1, 5; add t2, t2, t3; slli t3, t1, 4; add t2, t2, t3"
#guard bodyStateSlabStrideOps "s8" "t2" "t3"
  = "slli t2, s8, 6; slli t3, s8, 5; add t2, t2, t3; slli t3, s8, 4; add t2, t2, t3"

end EvmAsm.Codegen
