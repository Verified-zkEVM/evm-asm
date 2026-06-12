/-
  EvmAsm.Codegen.Programs.ChildFrameHandlers

  The CALL-family + CREATE-family + precompile child-frame handler module
  (the 6 child-frame opcodes: CREATE, CALL, CALLCODE, DELEGATECALL, CREATE2,
  STATICCALL). `childFrameHandlers` builds their `OpcodeHandlerSpec`s.

  The live descent that the SHIPPED guest registry (`callFrameGuestRegistry`)
  runs is `callDescendFallThrough` — the real CALL/CALLCODE/DELEGATECALL/
  STATICCALL sub-frame entry (depth gate, caller-balance gate, callee code
  resolution via `code_at_header_state_root`, `cd_desc` build + `jal
  call_frame_descend` frame switch). `callPushZeroFallThrough` is the legacy
  push-zero no-op fall-through, now used ONLY by the standalone dispatch probes
  (`tinyInterpRegistry` / `callFrameProbeRegistry`), NOT the verdict.
  CREATE/CREATE2 decode operands inline and run the bounded init-code
  mini-interpreter (see `createUnsupportedTail`); the active precompile
  addresses (0x01..0x05, BLS12-381 G1/G2/pairing/map) have real call tails.

  (Formerly `NoopChildFrame.lean` — renamed because these handlers are no
  longer no-ops. Originally split out of Noop.lean to stay under the
  file-size cap.)
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Modexp
import EvmAsm.Codegen.Programs.CreateRuntime
import EvmAsm.Codegen.Programs.PrecompileRuntime
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64


/-- M19 child-frame opcodes (CREATE, CALL, CALLCODE, DELEGATECALL,
    CREATE2, STATICCALL). Non-precompile CALL/CALLCODE/DELEGATECALL/STATICCALL
    route through the live descent (`callDescendFallThrough`): depth +
    caller-balance gates, callee code resolution, and a `call_frame_descend`
    sub-frame switch. CREATE-family paths decode operands, derive the target
    address, and run the bounded init-code mini-interpreter
    (`createUnsupportedTail`); later slices still own the per-address code
    deposit (.8b) and self-contained-gate activation (.8c).

    Net stack delta per opcode (= pop − push, multiplied by 32):

    - **CREATE (0xf0)**: pops 3 (value, offset, size), pushes 1 (addr).
      Net = +64 bytes (= 2 × 32).
    - **CALL (0xf1)** / **CALLCODE (0xf2)**: pops 7 (gas, to, value,
      in_off, in_size, out_off, out_size), pushes 1 (success).
      Net = +192 (= 6 × 32).
    - **DELEGATECALL (0xf4)** / **STATICCALL (0xfa)**: pops 6 (gas,
      to, in_off, in_size, out_off, out_size), pushes 1 (success).
      Net = +160 (= 5 × 32).
    - **CREATE2 (0xf5)**: pops 4 (value, offset, size, salt),
      pushes 1 (addr). Net = +96 (= 3 × 32).

    EVM stack-arg ordering: `μ_s[0]` (top) is `gas`/`value` per the
    Yellow Paper; the descent and the CREATE operand decode read the args
    at these fixed offsets from x12 (the parent stack top).

    **M27 update**: CALL / STATICCALL now recognize target
    addresses 0x01..0x05 as the basic precompile frame surface.
    SHA256 (0x02) hashes input bytes through `zkvm_sha256`,
    IDENTITY (0x04) copies input bytes to caller output memory, and
    both push success = 1. SHA256 and IDENTITY charge their exact
    word-linear inner precompile gas through the shared helper.
    MODEXP (0x05) handles the zero-length-header shortcut and charges
    its 500 minimum gas before returning empty output. RIPEMD160 (0x03)
    hashes input bytes through the software `zkvm_ripemd160` kernel
    (600 + 120/word gas, 32-byte left-padded returndata).

    **M27.2 update**: CALL / STATICCALL also recognize BLS12-381 G1
    active precompile addresses 0x0b (G1 ADD) and 0x0c (G1 MSM).
    The runtime path enforces execution-specs input-length gates and
    charges G1 ADD's fixed 375 gas plus G1 MSM's discounted per-pair gas.

    **M27.3 update**: CALL / STATICCALL also recognize BLS12-381 G2
    active precompile addresses 0x0d (G2 ADD) and 0x0e (G2 MSM).
    The runtime path enforces execution-specs input-length gates and
    charges G2 ADD's fixed 600 gas plus G2 MSM's discounted per-pair gas.

    **M27.4 update**: CALL / STATICCALL also recognize BLS12-381 pairing
    and map precompile addresses 0x0f (pairing), 0x10 (map-Fp-to-G1), and
    0x11 (map-Fp2-to-G2). Valid-length inputs invoke the linkable backend
    wrappers after charging pairing's per-pair gas and each map precompile's
    fixed gas. Current ziskemu safe-fails those wrappers, so EVM observes
    precompile failure until success-output slices land.

    **M27.1 update**: inactive near-zero addresses 0x12 and 0x101
    are not precompiles in the Amsterdam active set. Route them as
    absent-account calls with success = 1 and empty returndata so the
    precompile_absence fixtures do not stop at the dispatcher surface.

    **Known limitations** (documented in CODEGEN.md M19 narrative):
    - CREATE / CREATE2 derive the target address, reject code-or-nonce
      collisions when account-witness context is attached, and run the
      bounded init-code mini-interpreter, but the deployed code is not yet
      deposited/recorded per-address (.8b) nor activated in the
      self-contained gate (.8c).
    - `callPushZeroFallThrough` (the legacy push-zero no-op) is now the
      fall-through for the standalone dispatch probes only; the shipped
      guest descent is `callDescendFallThrough`. -/
def childFrameHandlers
    (callFallThrough callcodeFallThrough delegateFallThrough staticFallThrough : String) :
    List OpcodeHandlerSpec :=
  let createUnsupportedTail (netPopBytes : Nat) (hasSalt : Bool) : String :=
    -- Decode CREATE-family operands, derive the would-be target address using
    -- the shared CREATE/CREATE2 address helpers, and enforce the currently
    -- runtime-visible prechecks before later child/deposit execution slices.
    "  la x15, evm_precompile_frame\n" ++
    "  sd x0, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x14, 0(x12)\n" ++    -- value low limb
    "  ld x15, 32(x12)\n" ++   -- offset low limb
    "  ld x16, 64(x12)\n" ++   -- size low limb
    "  la x18, create_init_offset\n" ++
    "  sd x15, 0(x18)\n" ++
    "  la x18, create_init_size\n" ++
    "  sd x16, 0(x18)\n" ++
    (if hasSalt then
      "  ld x17, 96(x12)\n"   -- salt low limb; full salt is converted below
     else
      "") ++
    -- A nonzero high limb in size is outside the current static memory
    -- envelope. Offset high limbs matter only for nonempty initcode.
    "  ld x18, 72(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 80(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 88(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    -- fhsxz.2.4.2.61.8.3.6 / EIP-3860 + EIP-7907: init-code size > MAX_INIT_CODE_SIZE is an
    -- exceptional abort consuming all gas (execution-specs amsterdam system.py:85-86 raises
    -- OutOfGasError; MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE = 2 * 0x8000 = 0x10000 = 65536, per
    -- vm/interpreter.py — EIP-7907 doubled MAX_CODE_SIZE 0x6000->0x8000, so the bound is 65536,
    -- NOT the pre-Amsterdam 49152: init-code in (49152, 65536] is VALID and must execute, not
    -- be rejected). x16 is the full size (high limbs confirmed 0 above). The bound equals
    -- create_child_initcode's size (.zero 0x10000 = 65536), so a valid init-code (<= 65536) fits
    -- the staging buffer exactly while any larger (invalid) one is OOG-rejected before the copy,
    -- preventing the overflow into adjacent .data (create_child_returndata / create_child_code).
    "  li x18, 65536; bgtu x16, x18, .exit_outofgas\n" ++
    "  beqz x16, 1f\n" ++
    "  ld x18, 40(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 48(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 56(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  add x18, x15, x16\n" ++
    "  bltu x18, x15, .exit_outofgas\n" ++
    "  li x19, 0x10000\n" ++
    "  bltu x19, x18, .exit_outofgas\n" ++
    "1:\n" ++
    createInitcodeGasAsm
      (if hasSalt then "create2" else "create")
      "x16" "x18" "x19" "x23" hasSalt ++
    updateActiveMemorySizeAsm
      (if hasSalt then "create2_init" else "create_init")
      "x15" "x16" "x18" "x19" "x23" "x6" true ++
    -- Convert env.ADDRESS from stack-word representation to the canonical
    -- 20-byte big-endian input expected by address_compute_create*.
    "  la x18, create_sender_be\n" ++
    "  addi x19, x20, 19\n" ++
    "  li x23, 20\n" ++
    "2:\n" ++
    "  lbu x24, 0(x19)\n" ++
    "  sb x24, 0(x18)\n" ++
    "  addi x19, x19, -1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 2b\n" ++
    -- With account-witness context, enforce the executable-spec
    -- insufficient-balance zero-result branch before deriving success.
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 9f\n" ++
    "  la x18, create_value_be\n" ++
    "  addi x19, x12, 31\n" ++
    "  li x23, 32\n" ++
    "10:\n" ++
    "  lbu x24, 0(x19)\n" ++
    "  sb x24, 0(x18)\n" ++
    "  addi x19, x19, -1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 10b\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  ld a1, 584(x20)\n" ++
    "  la a2, create_sender_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  la a5, create_balance_be\n" ++
    "  jal x1, balance_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez t0, 7f\n" ++
    "  la x18, create_balance_be\n" ++
    "  la x19, create_value_be\n" ++
    "  li x23, 32\n" ++
    "11:\n" ++
    "  lbu x24, 0(x18)\n" ++
    "  lbu x25, 0(x19)\n" ++
    "  bltu x24, x25, 7f\n" ++
    "  bltu x25, x24, 9f\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 11b\n" ++
    "9:\n" ++
    -- Default to nonce 0 when no account-witness context is attached.
    "  la x18, create_nonce\n" ++
    "  sd x0, 0(x18)\n" ++
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 3f\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  la a2, create_sender_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  la a5, create_nonce\n" ++
    "  jal x1, nonce_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  beqz t0, 3f\n" ++
    "  la x18, create_nonce\n" ++
    "  sd x0, 0(x18)\n" ++
    "3:\n" ++
    "  la x18, create_nonce\n" ++
    "  ld x18, 0(x18)\n" ++
    "  li x19, -1\n" ++
    "  beq x18, x19, 7f\n" ++
    -- .61.8c-1: replace the bare pre-state nonce with the per-creator RUNNING nonce, so a SECOND
    -- CREATE by the same creator in this tx uses a distinct nonce (-> distinct address) -- the EVM
    -- increments the creator's nonce on each CREATE/CREATE2. x18 holds the witness pre-state nonce;
    -- create_creator_nonce_use seeds the per-creator table with it on the first CREATE and returns the
    -- running value (advancing the table; both CREATE and CREATE2 bump it). a0==x10 (the dispatcher
    -- PC) is clobbered by the call, so save/restore x10; the result (a0) is stored to create_nonce
    -- BEFORE restoring x10 (the #8608 lesson). create_creator_nonce_use preserves x12/x13/x20/x21.
    "  mv s10, x10\n" ++
    "  la a0, create_sender_be\n" ++
    "  mv a1, x18\n" ++
    "  jal x1, create_creator_nonce_use\n" ++
    "  la x18, create_nonce\n" ++
    "  sd a0, 0(x18)\n" ++
    "  mv x10, s10\n" ++
    (if hasSalt then
      -- Convert the CREATE2 salt stack word to canonical 32-byte big-endian.
      "  la x18, create_salt_be\n" ++
      "  addi x19, x12, 127\n" ++
      "  li x23, 32\n" ++
      "4:\n" ++
      "  lbu x24, 0(x19)\n" ++
      "  sb x24, 0(x18)\n" ++
      "  addi x19, x19, -1\n" ++
      "  addi x18, x18, 1\n" ++
      "  addi x23, x23, -1\n" ++
      "  bnez x23, 4b\n" ++
      "  mv s9, x13\n" ++
      "  mv s10, x10\n" ++
      "  mv s11, x12\n" ++
      "  la a0, create_sender_be\n" ++
      "  la a1, create_salt_be\n" ++
      "  ld a2, create_init_offset\n" ++
      "  add a2, x13, a2\n" ++
      "  ld a3, create_init_size\n" ++
      "  la a4, create_address_be\n" ++
      "  jal x1, address_compute_create2\n" ++
      "  mv x13, s9\n" ++
      "  mv x10, s10\n" ++
      "  mv x12, s11\n"
     else
      "  mv s9, x13\n" ++
      "  mv s10, x10\n" ++
      "  mv s11, x12\n" ++
      "  la a0, create_sender_be\n" ++
      "  ld a1, create_nonce\n" ++
      "  la a2, create_address_be\n" ++
      "  jal x1, address_compute_create\n" ++
      "  mv x13, s9\n" ++
      "  mv x10, s10\n" ++
      "  mv x12, s11\n") ++
    -- If an account-witness context is attached, apply the EIP-684
    -- code-or-nonce collision check to the derived target address.
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 6f\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  la a2, create_address_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  jal x1, has_code_or_nonce_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez t0, 7f\n" ++
    "  la x18, hcon_predicate\n" ++
    "  ld x18, 0(x18)\n" ++
    "  bnez x18, 7f\n" ++
    "6:\n" ++
    -- 5em02.2: debit the creator's LIVE balance (env+32 = .selfBalance, big-endian) by the
    -- endowment, so SELFBALANCE reads B-endowment after a CREATE (the transfer was inert ->
    -- false-reject for value-creating contracts). Reached only on the committing path (value
    -- gate passed, no address collision). ctx-gated (create_value_be valid, populated BE by
    -- the gate above) + borrow-guarded (the gate checked PRE-state balance; the live env+32 may
    -- be lower from an earlier same-frame value-op -> conservative skip on underflow). Same
    -- single-tx failure-rollback caveat as 5em02.1 (a CREATE that later reverts is not undone
    -- here). The created account's env+32 credit (init-code SELFBALANCE) is a follow-up.
    "  ld t3, 584(x20)\n  beqz t3, .Lcr_deb_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  addi a0, x20, 32\n" ++                            -- a0 = creator LIVE balance (env .selfBalance, BE)
    "  la a1, create_value_be\n" ++                      -- a1 = endowment (BE)
    "  la a2, create_creator_newbal\n" ++                -- a2 = out (= balance - endowment)
    "  jal ra, u256_sub_be\n" ++
    "  mv t0, a0\n" ++                                   -- t0 = borrow flag (before x10=a0 restore)
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  bnez t0, .Lcr_deb_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++   -- underflow -> skip
    "  la t0, create_creator_newbal\n  addi t1, x20, 32\n" ++
    "  ld t2, 0(t0)\n  sd t2, 0(t1)\n  ld t2, 8(t0)\n  sd t2, 8(t1)\n" ++
    "  ld t2, 16(t0)\n  sd t2, 16(t1)\n  ld t2, 24(t0)\n  sd t2, 24(t1)\n" ++
    ".Lcr_deb_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    createStageInitcodeFrameCallAsm (if hasSalt then 1 else 0) ++
    -- .61.8.3.5.3 (.5c): execute the staged init code in a REAL child frame via the full
    -- dispatch loop (create_frame_descend, .5a, reusing call_frame_descend), REPLACING the
    -- bounded mini-interpreter (create_execute_initcode_frame: STOP/MSTORE/MSTORE8/PUSH/RETURN/
    -- REVERT/INVALID only). The child now runs the full opcode set (SSTORE/arithmetic/CODECOPY/
    -- JUMP/...), so real constructors execute. On the child's RETURN the depth-aware
    -- returnRevertTail CREATE branch (.5b) validity-gates + deposits the returned bytes as the
    -- deployed code + pushes the DERIVED ADDRESS back to this frame (0 on invalid deploy / REVERT).
    -- create_frame_descend reads the endowment from x12 (stack top) itself; do NOT pass it in
    -- a0 (== x10 the PC) -- that would clobber the parent return PC the descent saves (#8608).
    -- a1 = netPopBytes (frame_return pops the CREATE args: 64 for CREATE / 96 for CREATE2).
    "  li a1, " ++ toString netPopBytes ++ "\n" ++
    "  jal x1, create_frame_descend\n" ++
    "  j .dispatch_loop\n" ++
    "7:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  sd x0, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "8:\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop"
  let basicPrecompileCallTail
      (tag : String) (netPopBytes inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat)
      (fallThroughAsm : String) : String :=
    -- Stack top at entry is the call gas word. The destination
    -- address is the next word for both CALL and STATICCALL. EVM
    -- address operands are masked to the low 160 bits: limb 1 and
    -- the low 32 bits of limb 2 participate in precompile dispatch,
    -- while bits 160..255 are ignored.
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  addi t0, x12, 32\n" ++
    "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    runtimeAccessWordToBe20Asm tag "t0" "t1" "t2" "t3" ++
    "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_charge\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    callMemoryExpansionGasAsm
      ("precompile_" ++ tag)
      inOffsetOff inSizeOff outOffsetOff outSizeOff ++
    "  ld x14, 32(x12)\n" ++
    "  ld x15, 40(x12)\n" ++
    "  bnez x15, 1f\n" ++
    "  ld x15, 48(x12)\n" ++
    "  slli x15, x15, 32\n" ++
    "  srli x15, x15, 32\n" ++
    "  bnez x15, 1f\n" ++
    "  li x15, 1\n" ++
    "  bltu x14, x15, 1f\n" ++
    "  li x15, 4\n" ++
    "  bgeu x15, x14, 11f\n" ++
    "  li x15, 5\n" ++
    "  beq x14, x15, .Lmodexp_zero_header_" ++ tag ++ "\n" ++
    "  li x15, 0x06\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_add\n" ++
    "  li x15, 0x07\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_mul\n" ++
    "  li x15, 0x08\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_pairing\n" ++
    "  li x15, 0x09\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_blake2f\n" ++
    "  li x15, 0x0a\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_kzg_point_eval\n" ++
    "  li x15, 0x0b\n" ++
    "  beq x14, x15, 13f\n" ++
    "  li x15, 0x0c\n" ++
    "  beq x14, x15, 14f\n" ++
    "  li x15, 0x0d\n" ++
    "  beq x14, x15, 15f\n" ++
    "  li x15, 0x0e\n" ++
    "  beq x14, x15, 16f\n" ++
    "  li x15, 0x0f\n" ++
    "  beq x14, x15, 17f\n" ++
    "  li x15, 0x10\n" ++
    "  beq x14, x15, 18f\n" ++
    "  li x15, 0x11\n" ++
    "  beq x14, x15, 19f\n" ++
    "  li x15, 0x12\n" ++
    "  beq x14, x15, 12f\n" ++
    "  li x15, 0x100\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_p256verify\n" ++
    "  li x15, 0x101\n" ++
    "  beq x14, x15, 12f\n" ++
    "  j 1f\n" ++
    "11:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 1\n" ++
    "  beq x14, x16, 29f\n" ++
    "  li x16, 2\n" ++
    "  beq x14, x16, 8f\n" ++
    "  li x16, 3\n" ++
    "  beq x14, x16, .L" ++ tag ++ "_ripemd160\n" ++
    "  li x16, 4\n" ++
    "  bne x14, x16, 7f\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    chargePrecompileWordGasAsm 15 3 "x17" "x16" "x22" ++
    "  sd x17, 8(x15)\n" ++       -- returndata length = full input size
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add x18, x13, x18\n" ++    -- x18 = identity input bytes
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++    -- x19 = caller output bytes
    -- Copy up to 256 bytes of returndata into the shared frame.
    "  mv x22, x18\n" ++
    "  addi x23, x15, 16\n" ++
    "  mv x24, x17\n" ++
    "  li x16, 256\n" ++
    "  bgeu x16, x24, 2f\n" ++
    "  mv x24, x16\n" ++
    "2:\n" ++
    "  beqz x24, 4f\n" ++
    "3:\n" ++
    "  lbu x16, 0(x22)\n" ++
    "  sb x16, 0(x23)\n" ++
    "  addi x22, x22, 1\n" ++
    "  addi x23, x23, 1\n" ++
    "  addi x24, x24, -1\n" ++
    "  bnez x24, 3b\n" ++
    -- Copy min(input_size, output_size) bytes to caller memory.
    "4:\n" ++
    "  mv x22, x17\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  bgeu x23, x22, 5f\n" ++
    "  mv x22, x23\n" ++
    "5:\n" ++
    "  beqz x22, 7f\n" ++
    "6:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 6b\n" ++
    "7:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  li x14, 1\n" ++
    "  sd x14, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    -- SHA256: digest = sha256(memory[in_offset .. in_offset+in_size)).
    -- The wrapper uses the LP64 a0/a1/a2 registers, so save the
    -- dispatcher code and stack pointers before setting up arguments.
    "8:\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a1, " ++ toString inSizeOff ++ "(x12)\n" ++
    chargePrecompileWordGasAsm 60 12 "a1" "x16" "x22" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x18\n" ++
    "  addi a2, x15, 16\n" ++
    "  jal x1, zkvm_sha256\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x22, 32\n" ++
    "  bgeu x23, x22, 9f\n" ++
    "  mv x22, x23\n" ++
    "9:\n" ++
    "  beqz x22, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "10:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 10b\n" ++
    "  j 7b\n" ++
    -- RIPEMD160 (0x03): digest = ripemd160(memory[in_offset .. in_offset+
    -- in_size)) via the software `zkvm_ripemd160` kernel (no ZisK accelerator
    -- exists for RIPEMD-160), word-linear 600 + 120/word gas, 32-byte
    -- returndata = 12 zero bytes ++ 20-byte hash (the EVM left-padded
    -- encoding, written by the kernel itself). Mirrors the SHA256 path above.
    ".L" ++ tag ++ "_ripemd160:\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a1, " ++ toString inSizeOff ++ "(x12)\n" ++
    chargePrecompileWordGasAsm 600 120 "a1" "x16" "x22" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x18\n" ++
    "  addi a2, x15, 16\n" ++
    "  jal x1, zkvm_ripemd160\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x22, 32\n" ++
    "  bgeu x23, x22, .L" ++ tag ++ "_ripemd_outcap\n" ++
    "  mv x22, x23\n" ++
    ".L" ++ tag ++ "_ripemd_outcap:\n" ++
    "  beqz x22, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    ".L" ++ tag ++ "_ripemd_copy:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_ripemd_copy\n" ++
    "  j 7b\n" ++
    -- ECRECOVER fixed gas, input staging, v/r/s gates, then (.62.2.5) the
    -- backend-pointer-gated recovery + 32-byte address output. Closures that
    -- leave `ecrecover_backend_ptr` 0 keep the legacy empty-returndata success.
    "29:\n" ++
    chargePrecompileGasConstAsm 3000 "x16" "x17" ++
    stageEcrecoverInputAsm inOffsetOff inSizeOff ++
    ecrecoverVGateAsm ++
    ecrecoverNonzeroRSGateAsm ++
    ecrecoverScalarOrderGateAsm ++
    ecrecoverRecoverAndOutputAsm outOffsetOff outSizeOff ++
    -- MODEXP header/gas path. execution-specs decodes missing length/header
    -- bytes as zero, rejects component lengths above 1024 before charging gas,
    -- and otherwise charges the EIP-2565/Osaka gas formula. Small nonzero
    -- components use a bounded software path; larger inputs still wait for
    -- the full zkvm_modexp output slice.
    ".Lmodexp_zero_header_" ++ tag ++ ":\n" ++
    modexpPrecompileGasAsm
      chargePrecompileGasAsm tag
      inOffsetOff inSizeOff outOffsetOff outSizeOff ++
    -- BN254 failed-call tail (kernel invalid input / child OOG): burn the
    -- forwarded EIP-150 allotment, push 0, resume. Reached only by branches
    -- from the two entries below (the preceding modexp block ends with jumps).
    bn254FailureStubAsm tag netPopBytes ++
    -- BN254 G1 ADD (EIP-196 ecAdd): fixed 150 gas charged from the child
    -- allotment, two 64-byte zero-padded G1 inputs, real Bn254CurveAdd-backed
    -- kernel. Invalid input (coord >= p / off-curve) is a precompile failure
    -- that consumes the full child allotment (execution-specs OutOfGasError).
    ".L" ++ tag ++ "_bn254_add:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 150\n" ++
    bn254ChargeGateAsm tag ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_add_p1") inOffsetOff inSizeOff precompileFrameBls12G1Input0Off 0 64 ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_add_p2") inOffsetOff inSizeOff precompileFrameBls12G1Input1Off 64 64 ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_g1_add\n" ++
    -- a0 IS x10: stash the kernel status before restoring the saved
    -- PC into x10 (the ecrecover-path landmine, #8721 stack notes).
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_bn254_add_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BN254 G1 MUL (EIP-196 ecMul): fixed 6000 gas, one 64-byte point plus
    -- one 32-byte scalar, real double-and-add kernel. Same failure mode.
    ".L" ++ tag ++ "_bn254_mul:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 6000\n" ++
    bn254ChargeGateAsm tag ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_mul_point") inOffsetOff inSizeOff precompileFrameBls12G1Input0Off 0 64 ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_mul_scalar") inOffsetOff inSizeOff precompileFrameBls12G1Input1Off 64 32 ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_g1_mul\n" ++
    -- a0 IS x10: stash the kernel status before restoring the saved
    -- PC into x10 (the ecrecover-path landmine, #8721 stack notes).
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_bn254_mul_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BN254 pairing (EIP-197): cost = 45000 + 34000 * floor(len / 192),
    -- charged from the EIP-150 child allotment. A gas-formula overflow,
    -- a non-multiple-of-192 length, or kernel-invalid input (coord >= p,
    -- off-curve, or Q outside the order-n subgroup) is a FAILED call that
    -- burns the allotment (execution-specs OutOfGasError).
    ".L" ++ tag ++ "_bn254_pairing:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 192\n" ++
    "  divu x22, x18, x16\n" ++
    "  li x16, 34000\n" ++
    "  mulhu x23, x22, x16\n" ++
    "  bnez x23, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  mul x16, x22, x16\n" ++
    "  li x23, 45000\n" ++
    "  add x16, x16, x23\n" ++
    "  bltu x16, x23, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bn254ChargeGateAsm tag ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 192\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_kfail\n" ++
    "  divu x22, x18, x16\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  mv a1, x22\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_pairing\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileSuccessBoolFromFrameAsm
      (tag ++ "_bn254_pairing_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BLAKE2F: exact 213-byte payload, then charge gas equal to the BE
    -- rounds field, then validate the final flag. The current runtime wrapper
    -- deterministic-fails, but the path is ready to expose the updated 64-byte
    -- state from h once a success-producing backend is available.
    ".L" ++ tag ++ "_blake2f:\n" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 213\n" ++
    "  bne x16, x17, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_blake2f_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 213 ++
    precompileFrameAddi "x18" precompileFrameBls12G2InputOff ++
    "  lbu x16, 0(x18)\n" ++
    "  slli x16, x16, 24\n" ++
    "  lbu x17, 1(x18)\n" ++
    "  slli x17, x17, 16\n" ++
    "  or x16, x16, x17\n" ++
    "  lbu x17, 2(x18)\n" ++
    "  slli x17, x17, 8\n" ++
    "  or x16, x16, x17\n" ++
    "  lbu x17, 3(x18)\n" ++
    "  or x16, x16, x17\n" ++
    chargePrecompileGasAsm "x16" "x17" ++
    "  lbu x17, 212(x18)\n" ++
    "  li x22, 1\n" ++
    "  bltu x22, x17, 1f\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  mv a0, x16\n" ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 4) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 68) ++
    precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 196) ++
    "  mv a4, x17\n" ++
    "  jal x1, zkvm_blake2f\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_blake2f_success") outOffsetOff outSizeOff (precompileFrameBls12G2InputOff + 4) ++
    -- KZG point evaluation: execution-specs rejects non-192-byte input before
    -- gas, then charges fixed 50000 gas before hash/proof validation.
    ".L" ++ tag ++ "_kzg_point_eval:\n" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 192\n" ++
    "  bne x16, x17, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    chargePrecompileGasConstAsm 50000 "x16" "x17" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_kzg_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 192 ++
    kzgVersionedHashGateAsm ++
    "  sb x0, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" (precompileFrameBls12G2InputOff + 96) ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 32) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 64) ++
    precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 144) ++
    precompileFrameAddi "a4" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_kzg_point_eval\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  beqz x16, 1f\n" ++
    precompileSuccessKzgPointEvalAsm
      (tag ++ "_kzg_point_eval_success") outOffsetOff outSizeOff ++
    -- P256VERIFY: execution-specs charges fixed gas before the exact length
    -- check. Invalid length and invalid signatures are successful precompile
    -- calls with empty returndata; backend EFAIL is precompile failure.
    ".L" ++ tag ++ "_p256verify:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    chargePrecompileGasConstAsm 6900 "x16" "x17" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 160\n" ++
    "  bne x16, x17, 12f\n" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_p256verify_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 160 ++
    "  sb x0, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G2InputOff ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 32) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 96) ++
    precompileFrameAddi "a3" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_secp256r1_verify\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez a0, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  beqz x16, 12f\n" ++
    precompileSuccessBoolFromFrameAsm
      (tag ++ "_p256verify_success") outOffsetOff outSizeOff precompileFrameBls12G2OutputOff ++
    "12:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G1 ADD (0x0b): exact 256-byte input, fixed 375 gas charged
    -- from the EIP-150 child allotment, real accelerator-backed kernel on the
    -- raw EIP-2537 input. Invalid input (bad pad / coord >= p / off-curve) is
    -- a FAILED call that burns the allotment (execution-specs InvalidParameter).
    "13:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 256\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 375\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_g1_add\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    "  j .L" ++ tag ++ "_blsg1_out\n" ++
    -- BLS12-381 G1 MSM (0x0c): nonempty multiple-of-160 input, per-pair
    -- discounted gas (bls12_g1_msm_discount_table) charged from the child
    -- allotment, real double-and-add kernel with the REAL order-n subgroup
    -- check on every input point (the G1 cofactor is not 1). Invalid input
    -- burns the allotment.
    "14:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 160\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bls12MsmCostAsm tag 160 12000 519 "bls12_g1_msm_discount_table" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 160\n" ++
    "  divu a1, x18, x17\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_g1_msm\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- Shared G1 success tail (ADD + MSM): expand the compact 96-byte result
    -- into EIP-2537 returndata (16 zero pad + 48-byte coordinate, twice) at
    -- frame+16, then copy min(128, out_size) to caller memory.
    ".L" ++ tag ++ "_blsg1_out:\n" ++
    "  addi x18, x15, 16\n" ++
    "  li x22, 16\n" ++
    ".L" ++ tag ++ "_blsg1_pad1:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_pad1\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G1OutputOff ++
    "  li x22, 48\n" ++
    ".L" ++ tag ++ "_blsg1_cx:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_cx\n" ++
    "  li x22, 16\n" ++
    ".L" ++ tag ++ "_blsg1_pad2:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_pad2\n" ++
    "  li x22, 48\n" ++
    ".L" ++ tag ++ "_blsg1_cy:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_cy\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 128\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 128\n" ++
    "  bgeu x22, x23, .L" ++ tag ++ "_blsg1_outcap\n" ++
    "  mv x23, x22\n" ++
    ".L" ++ tag ++ "_blsg1_outcap:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    ".L" ++ tag ++ "_blsg1_copyout:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, .L" ++ tag ++ "_blsg1_copyout\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G2 ADD (0x0d): exact 512-byte input, fixed 600 gas charged
    -- from the EIP-150 child allotment, real software-Fp2 kernel (complex
    -- accelerators + Arith384Mod Fermat inverse) on the raw EIP-2537 input.
    -- Invalid input burns the allotment (execution-specs InvalidParameter).
    "15:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 512\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 600\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G2AddOutputOff ++
    "  jal x1, zkvm_bls12_g2_add\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2AddOutputOff ++
    "  li x23, 4\n" ++
    "20:\n" ++
    "  li x22, 16\n" ++
    "21:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  li x22, 48\n" ++
    "22:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 22b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 20b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 23f\n" ++
    "  mv x23, x22\n" ++
    "23:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "24:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 24b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G2 MSM (0x0e): nonempty multiple-of-288 input, per-pair
    -- discounted gas (bls12_g2_msm_discount_table) charged from the child
    -- allotment, real software-Fp2 double-and-add kernel with the REAL
    -- order-n subgroup check on every input point. Invalid input burns the
    -- allotment.
    "16:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 288\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bls12MsmCostAsm tag 288 22500 524 "bls12_g2_msm_discount_table" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 288\n" ++
    "  divu a1, x18, x17\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_bls12_g2_msm\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2OutputOff ++
    "  li x23, 4\n" ++
    "20:\n" ++
    "  li x22, 16\n" ++
    "21:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  li x22, 48\n" ++
    "22:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 22b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 20b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 23f\n" ++
    "  mv x23, x22\n" ++
    "23:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "24:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 24b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 pairing (0x0f): nonempty multiple-of-384 input, gas
    -- 32600*k + 37700 charged from the EIP-150 child allotment, real
    -- py_ecc-mirroring FQ12 Miller-loop kernel on the raw EIP-2537 input
    -- (decode + on-curve + REAL subgroup checks on both sides in-kernel).
    -- Invalid input burns the allotment.
    "17:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 384\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 384\n" ++
    "  divu x17, x18, x16\n" ++
    "  li x16, 32600\n" ++
    "  mul x16, x17, x16\n" ++
    "  li x22, 32600\n" ++
    "  divu x22, x16, x22\n" ++
    "  bne x22, x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x22, 37700\n" ++
    "  add x16, x16, x22\n" ++
    "  bltu x16, x22, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 384\n" ++
    "  divu a1, x18, x17\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_pairing\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 pairing returns a 32-byte boolean word: 31 zero bytes followed
    -- by the backend `verified` byte.
    "  sd x0, 16(x15)\n" ++
    "  sd x0, 24(x15)\n" ++
    "  sd x0, 32(x15)\n" ++
    "  sd x0, 40(x15)\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G1OutputOff ++ "(x15)\n" ++
    "  sb x16, 47(x15)\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 32\n" ++
    "  bgeu x22, x23, 22f\n" ++
    "  mv x23, x22\n" ++
    "22:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "23:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 23b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 map-Fp-to-G1: execution-specs requires exactly one
    -- 64-byte Fp field element; the compact 48-byte field payload starts
    -- after the 16-byte EIP-2537 zero pad.
    "18:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 64\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 5500\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_map_fp_to_g1\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g1_to_bytes`: each compact 48-byte coordinate is left-padded
    -- to a 64-byte big-endian field element.
    "  sd x0, 16(x15)\n" ++
    "  sd x0, 24(x15)\n" ++
    precompileFrameAddi "x17" precompileFrameBls12G1OutputOff ++
    "  addi x18, x15, 32\n" ++
    "  li x19, 48\n" ++
    "34:\n" ++
    "  lbu x16, 0(x17)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 34b\n" ++
    "  sd x0, 80(x15)\n" ++
    "  sd x0, 88(x15)\n" ++
    precompileFrameAddi "x17" (precompileFrameBls12G1OutputOff + 48) ++
    "  addi x18, x15, 96\n" ++
    "  li x19, 48\n" ++
    "35:\n" ++
    "  lbu x16, 0(x17)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 35b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 128\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 128\n" ++
    "  bgeu x22, x23, 36f\n" ++
    "  mv x23, x22\n" ++
    "36:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "37:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 37b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 map-Fp2-to-G2: execution-specs requires exactly one
    -- 128-byte Fp2 element. Project the two compact 48-byte Fp chunks into
    -- the G2-class compact input lane before calling the backend.
    "19:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 128\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 23800\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_bls12_map_fp2_to_g2\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2OutputOff ++
    "  li x23, 4\n" ++
    "34:\n" ++
    "  li x22, 16\n" ++
    "35:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 35b\n" ++
    "  li x22, 48\n" ++
    "36:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 36b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 34b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 37f\n" ++
    "  mv x23, x22\n" ++
    "37:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "38:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 38b\n" ++
    "  j 7b\n" ++
    "1:\n" ++ fallThroughAsm
  [ { label := "h_CREATE"
    , opcodes := [0xf0]
    , preBody := stackUnderflowGuardAsm 3 ++ "\n"
    , body := []
    , tail := .custom (createUnsupportedTail 64 false) }
  , { label := "h_CALL"
    , opcodes := [0xf1]
    , preBody := stackUnderflowGuardAsm 7 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "call_target" 192 96 128 160 192 callFallThrough) }
  , { label := "h_CALLCODE"
    , opcodes := [0xf2]
    , preBody := stackUnderflowGuardAsm 7 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "callcode_target" 192 96 128 160 192 callcodeFallThrough) }
  , { label := "h_DELEGATECALL"
    , opcodes := [0xf4]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "delegatecall_target" 160 64 96 128 160 delegateFallThrough) }
  , { label := "h_CREATE2"
    , opcodes := [0xf5]
    , preBody := stackUnderflowGuardAsm 4 ++ "\n"
    , body := []
    , tail := .custom (createUnsupportedTail 96 true) }
  , { label := "h_STATICCALL"
    , opcodes := [0xfa]
    , preBody := stackUnderflowGuardAsm 6 ++ "\n"
    , body := []
    , tail := .custom (basicPrecompileCallTail "staticcall_target" 160 64 96 128 160 staticFallThrough) } ]

/-- M20 arithmetic no-op handlers.

    The original M20 placeholders covered MULMOD and EXP. Both have now moved
    to real dispatcher handlers in `EvmAsm/Codegen/Programs/Evm.lean`, so this
    list is intentionally empty and remains only to keep the registry assembly
    expression stable. -/
def arithNoopHandlers : List OpcodeHandlerSpec := []

/-- The original non-precompile CALL/STATICCALL fall-through: the call no-ops —
    pop the args, push a `0` (failure) result, advance the PC, and resume. Used by
    `tinyInterpRegistry` (the standalone dispatch probes keep this behaviour). -/
def callPushZeroFallThrough (netPopBytes : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop"

/-- The real non-precompile CALL/STATICCALL descent (bead .61.6). At the `1:`
    fall-through (regs: x10=parent pc at the CALL, x12=parent stack top with the
    args, x13=parent memory, x20=parent env, x21=parent code base), this:
      1. clears the precompile frame;
      2. depth gate: `evm_call_depth >= 1024` → push 0 (fail);
      2b. balance gate (value-bearing CALL/CALLCODE): if the caller (frame ADDRESS,
         env+0) balance < transfer value → push 0 (fail, no descent), per EVM
         `generic_call`. Skipped for STATICCALL/DELEGATECALL (no value), value==0,
         or when no account-witness context is attached (env+584 == 0);
      3. resolves the callee bytecode via `code_at_header_state_root` (witness ctx
         from env+576..616). It preserves x20/x21 but clobbers the a-regs (x10/x12/
         x13), so those are saved across the call. status 2 (EMPTY_CODE / EOA) →
         push 1 (the call succeeds, runs no code); status 1/3/5 → push 0;
      4. status 0: fill `cd_desc` and `jal call_frame_descend` (frame switch), then
         `j .dispatch_loop` to run the child at its frame.
    Used only by `callFrameGuestRegistry`. `tag` makes the local labels unique per
    call type. `valueOff` is the stack offset of the call value (unused/0 for the
    value-less kinds). `mode` selects the message-call kind (matching
    `call_frame_set_call_env`): `0 = CALL`, `1 = STATICCALL`, `2 = CALLCODE`,
    `3 = DELEGATECALL`. The value-bearing kinds (CALL, CALLCODE) run the balance
    gate and forward value/stipend; STATICCALL/DELEGATECALL carry no value
    (DELEGATECALL inherits the parent's CALLVALUE inside `call_frame_set_call_env`).
    Gas: `call_frame_descend` forwards the EIP-150 63/64 + stipend to the child;
    the caller-side value/new-account/parent charge is a follow-up (the descent is
    inert in the single-tx verdict). -/
def callDescendFallThrough
    (tag : String) (netPopBytes valueOff inOff inSize outOff outSize : Nat)
    (mode : Nat) : String :=
  let np := toString netPopBytes
  -- value-bearing message calls (CALL=0, CALLCODE=2) charge value/balance; the
  -- value-less kinds (STATICCALL=1, DELEGATECALL=3) skip the balance gate.
  let valueBearing := mode == 0 || mode == 2
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  -- depth gate
  "  la t0, evm_call_depth\n" ++
  "  ld t0, 0(t0)\n" ++
  "  li t1, 1024\n" ++
  "  bgeu t0, t1, .Lcd_fail_" ++ tag ++ "\n" ++
  -- balance gate (value-bearing CALL only): EVM `generic_call` rejects the call
  -- with a pushed 0 when the caller's balance is below the transfer value
  -- (vm/instructions/system.py; the value is NOT transferred and the sub-call is
  -- not entered). Mirrors the verified CREATE-path caller-balance lookup: the
  -- caller is the current frame's ADDRESS (env+0) as canonical 20-byte BE, and
  -- the value is the stack word at valueOff. STATICCALL has no value (skipped).
  (if !valueBearing then "" else
    "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  beqz t3, .Lcd_balok_" ++ tag ++ "\n" ++       -- value == 0: no transfer, skip
    "  ld t3, 584(x20)\n" ++
    "  beqz t3, .Lcd_balok_" ++ tag ++ "\n" ++        -- no account-witness ctx: skip
    -- caller address env+19..env+0 -> cd_caller_be (canonical 20-byte big-endian)
    "  la t0, cd_caller_be\n" ++
    "  addi t1, x20, 19\n" ++
    "  li t2, 20\n" ++
    ".Lcd_addr_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n" ++
    "  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_addr_" ++ tag ++ "\n" ++
    -- value word x12+valueOff (32 B) -> cd_value_be (big-endian: read +31..+0)
    "  la t0, cd_value_be\n" ++
    "  addi t1, x12, " ++ toString (valueOff+31) ++ "\n" ++
    "  li t2, 32\n" ++
    ".Lcd_val_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n" ++
    "  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_val_" ++ tag ++ "\n" ++
    -- balance_at_header_state_root(caller) -> cd_balance_be. Save x10/x12/x13
    -- (helper clobbers the a-regs that alias them); it preserves x20/x21.
    "  addi sp, sp, -32\n" ++
    "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n" ++
    "  ld a1, 584(x20)\n" ++
    "  la a2, cd_caller_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  la a5, cd_balance_be\n" ++
    "  jal ra, balance_at_header_state_root\n" ++
    "  mv t2, a0\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n" ++
    "  addi sp, sp, 32\n" ++
    "  bnez t2, .Lcd_fail_" ++ tag ++ "\n" ++         -- lookup failed/absent -> balance 0 < value
    -- compare cd_balance_be vs cd_value_be (32-byte big-endian, MSB first)
    "  la t0, cd_balance_be\n" ++
    "  la t1, cd_value_be\n" ++
    "  li t2, 32\n" ++
    ".Lcd_cmp_" ++ tag ++ ":\n" ++
    "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n" ++
    "  bltu t3, t4, .Lcd_fail_" ++ tag ++ "\n" ++     -- balance < value: insufficient
    "  bltu t4, t3, .Lcd_balok_" ++ tag ++ "\n" ++    -- balance > value: sufficient
    "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
    "  bnez t2, .Lcd_cmp_" ++ tag ++ "\n" ++
    ".Lcd_balok_" ++ tag ++ ":\n" ++
    -- 5em02.1: debit the caller's LIVE balance (env+32 = .selfBalance, big-endian) by the
    -- transferred value so SELFBALANCE reads B-V mid-execution. The transfer was inert, so
    -- SELFBALANCE read the staged pre-state balance -> false-reject for value-moving
    -- contracts. CALL (mode 0) only: CALLCODE keeps the value in the caller's own context
    -- (transfer-to-self, no balance change). Guards: value!=0 + account-witness ctx present
    -- (so cd_value_be is the valid BE value the gate populated above) + borrow-check (the
    -- gate verified PRE-state balance>=value; the LIVE env+32 may be lower from an earlier
    -- value-CALL in this frame -> skip on underflow, conservative no-op). u256_sub_be
    -- clobbers a-regs aliasing x10/x12/x13; x20 is preserved.
    (if mode != 0 then "" else
      "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
      "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
      "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
      "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
      "  beqz t3, .Lcd_deb_done_" ++ tag ++ "\n" ++       -- value == 0: no debit
      "  ld t3, 584(x20)\n  beqz t3, .Lcd_deb_done_" ++ tag ++ "\n" ++   -- no ctx -> cd_value_be stale -> skip
      -- self-call guard: if the callee (x12+32, 20-byte BE) == the caller (cd_caller_be,
      -- the gate's 20-byte BE), the value returns to self -> net-zero. The per-frame env
      -- model would otherwise leave the caller frame at B-V after return -> false-reject.
      "  la t0, cd_caller_be\n  addi t1, x12, 32\n  li t2, 20\n" ++
      ".Lcd_selfchk_" ++ tag ++ ":\n" ++
      "  beqz t2, .Lcd_deb_done_" ++ tag ++ "\n" ++        -- all 20 bytes equal -> self-call -> skip
      "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n  bne t3, t4, .Lcd_notself_" ++ tag ++ "\n" ++
      "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  j .Lcd_selfchk_" ++ tag ++ "\n" ++
      ".Lcd_notself_" ++ tag ++ ":\n" ++
      "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
      "  addi a0, x20, 32\n" ++                            -- a0 = caller LIVE balance (env .selfBalance, BE)
      "  la a1, cd_value_be\n" ++                          -- a1 = transferred value (BE)
      "  la a2, cd_caller_newbal\n" ++                     -- a2 = out (= balance - value)
      "  jal ra, u256_sub_be\n" ++
      "  mv t0, a0\n" ++                                   -- t0 = borrow flag (before x10=a0 restore)
      "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
      "  bnez t0, .Lcd_deb_done_" ++ tag ++ "\n" ++        -- underflow (live < value): conservative skip
      "  la t0, cd_caller_newbal\n  addi t1, x20, 32\n" ++
      "  ld t2, 0(t0)\n  sd t2, 0(t1)\n  ld t2, 8(t0)\n  sd t2, 8(t1)\n" ++
      "  ld t2, 16(t0)\n  sd t2, 16(t1)\n  ld t2, 24(t0)\n  sd t2, 24(t1)\n" ++
      ".Lcd_deb_done_" ++ tag ++ ":\n") ++
    -- i3djw.1: record the value-transfer NON-STORAGE effect for the callee so the
    -- all-accounts non-storage comparator (i3djw.3) can validate it against the BAL.
    -- The callee receives `value`; record (callee, pre_balance, pre+value, nonce, nonce)
    -- — value transfer does not bump the callee nonce. INERT until i3djw.3 wires the
    -- comparator (nothing reads exec_nonstorage_effect_log yet), so over-recording a
    -- value-CALL that later fails code resolution is harmless now; success-gating is
    -- deferred to i3djw.3. a0/a2/a3 alias x10/x12/x13 (PC/stack/mem-base), so the
    -- dispatcher invariants are saved/restored around every helper call.
    "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
    "  beqz t3, .Lcd_nse_done_" ++ tag ++ "\n" ++       -- value == 0: no transfer, skip
    -- copy the 20-byte callee address (x12+32) into nse_callee_be (survives x12 clobber)
    "  addi t0, x12, 32\n  la t1, nse_callee_be\n  li t2, 20\n" ++
    ".Lcd_nse_cpaddr_" ++ tag ++ ":\n" ++
    "  beqz t2, .Lcd_nse_cpaddr_d_" ++ tag ++ "\n" ++
    "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  j .Lcd_nse_cpaddr_" ++ tag ++ "\n" ++
    ".Lcd_nse_cpaddr_d_" ++ tag ++ ":\n" ++
    -- pre fields: account_at_header_state_root(callee) -> nse_acct (nonce@0, balance@8)
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, nse_callee_be\n  li a3, 20\n  ld a4, 592(x20)\n  ld a5, 600(x20)\n  la a6, nse_acct\n" ++
    "  jal ra, account_at_header_state_root\n" ++
    "  mv t0, a0\n" ++                                  -- status (capture before restoring x10=a0)
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  bnez t0, .Lcd_nse_done_" ++ tag ++ "\n" ++       -- callee absent/err -> skip (conservative)
    -- post_balance = pre_balance (nse_acct+8) + value (cd_value_be, populated above)
    "  addi sp, sp, -16\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n" ++
    "  la a0, nse_acct\n  addi a0, a0, 8\n  la a1, cd_value_be\n  la a2, nse_post_bal\n" ++
    "  jal ra, u256_add_be\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  addi sp, sp, 16\n" ++
    -- append (addr, pre_balance, post_balance, pre_nonce, post_nonce)
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la t0, nse_acct\n  ld a3, 0(t0)\n  mv a4, a3\n" ++   -- pre_nonce == post_nonce (unchanged by value transfer)
    "  la a0, nse_callee_be\n  la a1, nse_acct\n  addi a1, a1, 8\n  la a2, nse_post_bal\n" ++
    "  jal ra, record_nonstorage_effect\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    -- fhsxz.2.4.2.63.1.6.2.6: EIP-7708 emit_transfer_log for this CALL value move, so the
    -- value-bearing tx's receipt logs/bloom are complete. from = parent ADDRESS (env+0),
    -- to = callee (x12+32), value = value word (x12+valueOff), ALL passed as raw EVM stack
    -- words (LE-limb). The log materializer (log_records_encode_rlp / materialize_log_records)
    -- byte-reverses each 32B topic slot to the canonical BE topic, and the appender byte-
    -- reverses the value into the descriptor's canonical-BE amount — so every field must enter
    -- in stack-word form. `from` (env.ADDRESS) already is; the callee `to` arg and the value
    -- arg on the parent stack are the same form, so they pass verbatim. (The earlier BE right-
    -- aligned `to` into [12:32] and BE `cd_value_be` produced wrong-order topics/data: the
    -- materializer reverses the WHOLE 32B slot, so the address must sit in the low 20 bytes,
    -- not the high 12. Latent until receipt-consensus enforcement un-gates.)
    -- x12 = parent stack top here (restored after record_nonstorage_effect above); the appender
    -- reads through the a1/a2 pointers into EVM memory, which its own sp frame does not disturb.
    -- Still inside the value!=0 guard. eip7708_append_transfer_log no-ops on a zero value and
    -- (on the 1024-descriptor cap) drops without appending; ignore its status (the receipts
    -- encoder gates conservatively on the descriptor/data overflow flags).
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  mv a0, x20\n  addi a1, x12, 32\n  addi a2, x12, " ++ toString valueOff ++ "\n" ++
    "  jal ra, eip7708_append_transfer_log\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    ".Lcd_nse_done_" ++ tag ++ ":\n") ++
  -- resolve callee code (save x10/x12/x13 — code_at_header_state_root clobbers a-regs)
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  addi a2, x12, 32\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  ld a5, 608(x20)\n" ++
  "  ld a6, 616(x20)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  mv t2, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  beqz t2, .Lcd_descend_" ++ tag ++ "\n" ++
  "  li t3, 2\n" ++
  "  beq t2, t3, .Lcd_empty_" ++ tag ++ "\n" ++
  -- fail (status 1/3/5): pop args, push 0
  ".Lcd_fail_" ++ tag ++ ":\n" ++
  "  addi x12, x12, " ++ np ++ "\n" ++
  "  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop\n" ++
  -- empty code (EOA): the call succeeds, runs nothing → push 1
  ".Lcd_empty_" ++ tag ++ ":\n" ++
  "  addi x12, x12, " ++ np ++ "\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop\n" ++
  -- descend (status 0): build the call descriptor then switch frames
  ".Lcd_descend_" ++ tag ++ ":\n" ++
  "  ld t0, 608(x20)\n" ++
  "  la t1, cahsr_code_offset; ld t1, 0(t1)\n" ++
  "  add t0, t0, t1\n" ++                       -- t0 = code_ptr
  "  la t1, cahsr_code_length; ld t1, 0(t1)\n" ++ -- t1 = code_len
  "  la t2, cd_desc\n" ++
  "  addi t3, x12, 32\n  sd t3, 0(t2)\n" ++      -- to_ptr
  -- value_ptr: the value-bearing kinds (CALL/CALLCODE) pass the stack value;
  -- STATICCALL/DELEGATECALL pass the zero word (set_call_env zeroes/inherits it).
  (if valueBearing then
     "  addi t3, x12, " ++ toString valueOff ++ "\n  sd t3, 8(t2)\n"
   else
     "  la t3, cd_zero_word\n  sd t3, 8(t2)\n") ++
  -- desc+16 = mode (0 CALL / 1 STATICCALL / 2 CALLCODE / 3 DELEGATECALL), read by
  -- call_frame_set_call_env via call_frame_descend.
  "  li t3, " ++ toString mode ++ "\n  sd t3, 16(t2)\n" ++
  "  ld t3, " ++ toString inOff ++ "(x12)\n  sd t3, 24(t2)\n" ++   -- argsOff
  "  ld t3, " ++ toString inSize ++ "(x12)\n  sd t3, 32(t2)\n" ++  -- argsLen
  "  ld t3, " ++ toString outOff ++ "(x12)\n  sd t3, 40(t2)\n" ++  -- outOff
  "  ld t3, " ++ toString outSize ++ "(x12)\n  sd t3, 48(t2)\n" ++ -- outSize
  "  li t3, " ++ np ++ "\n  sd t3, 56(t2)\n" ++                    -- netPopBytes
  "  sd t0, 64(t2)\n" ++                                           -- code_ptr
  "  sd t1, 72(t2)\n" ++                                           -- code_len
  "  ld t3, 0(x12)\n  sd t3, 80(t2)\n" ++                          -- requested_gas
  (if !valueBearing then
     "  sd x0, 88(t2)\n"                                           -- value_nonzero = 0
   else
     "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
     "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
     "  snez t3, t3\n  sd t3, 88(t2)\n") ++                        -- value_nonzero
  "  la a1, cd_desc\n" ++
  "  jal ra, call_frame_descend\n" ++
  "  j .dispatch_loop"

end EvmAsm.Codegen
