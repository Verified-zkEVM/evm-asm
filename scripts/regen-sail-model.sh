#!/usr/bin/env bash
# regen-sail-model.sh — reproducibly regenerate the scoped zkVM RISC-V Lean model.
#
# STATUS: VALIDATED END-TO-END (2026-06-25). The pins, flags, and invocation below
# were exercised: generation completes AND the result builds patch-free against
# lean-sail v4 on the project's lean4 v4.30.0-rc1 (lake build, 84/84 jobs, exit 0 —
# incl. InstsEnd/DecodeExt/Step/Model). See docs/agents/sail-regen-spike.md.
# DIRECTION (maintainer 2026-06-25): track CURRENT upstream — Sail 0.20.2 +
# sail-riscv release tag + external lean-sail v4. P2 vendors the output and wires
# this into check-sail-pin.sh.
#
# KEY FACTS (all verified):
#   * Sail installs from opam (`opam install sail.0.20.2`) — no build-from-source.
#   * !! MUST build Sail on OCaml >= 5.2 !! On OCaml 4.14.2 the Lean backend
#     STACK-OVERFLOWS on the sail-riscv model (rems-project/sail#1674: pre-5.2 stdlib
#     isn't tail-recursive). Use an OCaml 5.x opam switch. Generation cost on 5.4.1:
#     ~9-13 min wall, ~7 GB RSS (one-time; --memo-z3 speeds repeats).
#   * sail-riscv's generated model imports the EXTERNAL lean-sail package
#     (RiscvExtras: `import Sail.Sail`) — no inlined runtime. Emits `require Sail
#     rev=v4` and `lean-toolchain = v4.29.0` (scaffolding only). lean-sail v4
#     (79b4d08) BUILDS ON v4.30.0-rc1, so the project keeps v4.30.0-rc1 — NO bump.
#   * Module scoping is POSITIONAL after the project file (no --module flag even in
#     0.20.2). sail-riscv main ALSO exposes -DSAIL_MODULES as a cmake cache var.
#   * Flags MUST match sail-riscv's cmake lean target exactly — esp. all THREE
#     `--lean-non-beq-type` (instruction, ExecutionResult, Step); omitting the
#     latter two makes ExecutionResult try to `deriving BEq` and fail.
set -euo pipefail

MODE="${1:---plan}"

# --- Pins (mirror sail-import/PROVENANCE.toml [target]) ------------------------
SAIL_RISCV_TAG="2026-06-22-b5a2182"   # latest sail-riscv RELEASE tag (requires Sail >=0.20.1); validated on main @ e123b61 (~equiv)
SAIL_SWITCH="${SAIL_SWITCH:-sail5}"   # opam switch with sail 0.20.2 built on OCaml >= 5.2 (NOT the 4.14.2 default!)
SAIL_REQUIRED_VER="0.20.1"
LEAN_SAIL_REV="v4"                    # external runtime the model requires (= 79b4d08); builds on v4.30.0-rc1

# z3 (4.15.3) is required by Sail's typechecker and is NOT on PATH by default.
# NOTE: this nix-store path is machine-specific — parameterize (env/discovery)
# before any CI regen gate. Override via Z3_BIN_DIR.
Z3_BIN_DIR="${Z3_BIN_DIR:-/nix/store/x6z3sjmccszacl1xvdlpi7bd4ps7mhci-z3-4.15.3/bin}"
SAIL_BIN_DIR="${SAIL_BIN_DIR:-$HOME/.opam/${SAIL_SWITCH}/bin}"

# --- The scoped RV64IM module selection (POSITIONAL) ---------------------------
# `main` reaches the fetch/decode/step loop via postlude; I_insts / M_insts add the
# integer + M instruction (scattered) clauses. NOTE: `sys` unavoidably drags in the
# V/FD register *state* (~163 ctors, not minimal). Whether to scope at all (vs
# full-model + a coverage gate) is an open P2 question — scoping did NOT reduce
# generation memory.
SAIL_MODULES=(main I_insts M_insts)

CONFIG_FILE="sail-import/riscv64im_zicclsm.json"   # NOTE: produced vs old 1760ee2 schema; P2 must REGENERATE/REVALIDATE against the tag's schema

# Lean backend flags — EXACTLY mirroring sail-riscv model/CMakeLists.txt's lean target.
lean_flags() {
  local outdir="$1"
  printf '%s\n' \
    --lean --lean-output-dir "$outdir" --lean-force-output \
    --lean-non-beq-type instruction --lean-non-beq-type ExecutionResult --lean-non-beq-type Step \
    --lean-noncomputable \
    --lean-noncomputable-function encdec_forwards \
    --lean-noncomputable-function encdec_backwards \
    --lean-noncomputable-function encdec_forwards_matches \
    --lean-noncomputable-function encdec_backwards_matches \
    --lean-noncomputable-function encdec_compressed_forwards \
    --lean-noncomputable-function encdec_compressed_backwards \
    --lean-noncomputable-function encdec_compressed_forwards_matches \
    --lean-noncomputable-function encdec_compressed_backwards_matches \
    --lean-import-file ../handwritten_support/RiscvExtras.lean
}

print_plan() {
  cat <<EOF
=== regen-sail-model.sh — PLAN (no changes made) ===

Prereqs:
  * opam switch "${SAIL_SWITCH}" = sail 0.20.2 built on OCaml >= 5.2 at ${SAIL_BIN_DIR}
    (create: opam switch create ${SAIL_SWITCH} ocaml-base-compiler.5.4.1 && \\
             opam install --switch ${SAIL_SWITCH} sail.0.20.2)
    !! Do NOT use a 4.14.x switch — the Lean backend stack-overflows (sail#1674).
  * z3 4.15.3 at ${Z3_BIN_DIR}  (machine-specific path — parameterize for CI)
  * network access to clone github.com/riscv/sail-riscv @ ${SAIL_RISCV_TAG}

1. Clone + checkout sail-riscv at the release tag:
     git clone https://github.com/riscv/sail-riscv.git
     git -C sail-riscv checkout ${SAIL_RISCV_TAG}

2. cmake CONFIGURE ONLY (emits config schema + finds toolchain; no build):
     cmake -S sail-riscv -B sail-riscv/build -DCMAKE_BUILD_TYPE=Release

3. Generate the scoped Lean model (positional modules; imports EXTERNAL lean-sail
   ${LEAN_SAIL_REV}; ~9-13 min / ~7 GB):
     cd sail-riscv/model
     sail --strict-var --strict-bitvector --strict-exponentials \\
          --require-version ${SAIL_REQUIRED_VER} --memo-z3 --memo-z3-path <cache> \\
          <lean-flags: incl. all 3 --lean-non-beq-type> \\
          --variable "TERMINATION_FILE = true" --config <repo>/${CONFIG_FILE} \\
          riscv.sail_project ${SAIL_MODULES[*]}

   Decode is bv_decide-free (no --lean-matchbv).

4. VENDOR: copy output under vendor/sail-riscv-zkvm-lean/, set lean-toolchain to the
   project's v4.30.0-rc1 and the lakefile `require Sail` to lean-sail ${LEAN_SAIL_REV}
   (the emitted v4.29.0/git scaffolding is discarded). Then repoint the project off
   the dhsorens fork and re-point the 51 *_sail_equiv lemmas (mind bool_to_bit ->
   bool_to_bits; diff regenerated-vs-old first). VALIDATED: this builds patch-free.

Run with:  scripts/regen-sail-model.sh --run <out-dir>
EOF
}

do_run() {
  local outdir="${1:?usage: $0 --run <out-dir>}"
  local repo_root; repo_root="$(cd "$(dirname "$0")/.." && pwd)"
  local cfg="${repo_root}/${CONFIG_FILE}"
  [[ -f "$cfg" ]] || { echo "ERROR: config not found: $cfg" >&2; exit 2; }

  export PATH="${Z3_BIN_DIR}:${SAIL_BIN_DIR}:${PATH}"
  command -v sail >/dev/null || { echo "ERROR: sail not on PATH (expected in ${SAIL_BIN_DIR}; build on OCaml>=5.2)" >&2; exit 2; }
  command -v z3   >/dev/null || { echo "ERROR: z3 not on PATH (expected in ${Z3_BIN_DIR})" >&2; exit 2; }

  local work; work="$(mktemp -d)"; local zcache="${work}/z3cache"; mkdir -p "$zcache"
  echo ">> cloning sail-riscv @ ${SAIL_RISCV_TAG} into ${work}" >&2
  git clone --quiet https://github.com/riscv/sail-riscv.git "${work}/sail-riscv"
  git -C "${work}/sail-riscv" checkout --quiet "${SAIL_RISCV_TAG}"

  echo ">> cmake configure (no build)" >&2
  cmake -S "${work}/sail-riscv" -B "${work}/sail-riscv/build" -DCMAKE_BUILD_TYPE=Release >/dev/null

  mkdir -p "$outdir"
  echo ">> generating scoped Lean model: ${SAIL_MODULES[*]} (~9-13 min)" >&2
  ( cd "${work}/sail-riscv/model"
    mapfile -t LF < <(lean_flags "$outdir")
    sail --strict-var --strict-bitvector --strict-exponentials --require-version "${SAIL_REQUIRED_VER}" \
      --memo-z3 --memo-z3-path "$zcache" \
      "${LF[@]}" \
      --variable "TERMINATION_FILE = true" \
      --config "$cfg" \
      riscv.sail_project "${SAIL_MODULES[@]}" )

  echo ">> done. .lean files: $(find "$outdir" -name '*.lean' | wc -l) in ${outdir}" >&2
}

case "$MODE" in
  --plan) print_plan ;;
  --run)  shift; do_run "${1:-}" ;;
  *) echo "usage: $0 [--plan|--run <out-dir>]" >&2; exit 1 ;;
esac
