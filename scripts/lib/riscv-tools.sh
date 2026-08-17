# shellcheck shell=bash
# Shared RISC-V binutils probes for .sh CI wrappers (GH #12503).
#
# Source from repo-root scripts:
#   # shellcheck source=lib/riscv-tools.sh
#   source "$(dirname "$0")/lib/riscv-tools.sh"
#
# Loud skip (exit 0) when the toolchain is absent — never silent.
# Bash 3-compatible (macOS /bin/bash): no ${var^^}, no dependency on `tr`
# being on a scrubbed PATH.
_riscv_upper() {
  case "$1" in
    as) printf 'AS' ;;
    ld) printf 'LD' ;;
    nm) printf 'NM' ;;
    objdump) printf 'OBJDUMP' ;;
    objcopy) printf 'OBJCOPY' ;;
    readelf) printf 'READELF' ;;
    *)
      # Fallback for unexpected tool names: ASCII fold without external `tr`.
      local s="$1" i c out=""
      i=0
      while [[ $i -lt ${#s} ]]; do
        c="${s:$i:1}"
        case "$c" in
          a) out+=A ;; b) out+=B ;; c) out+=C ;; d) out+=D ;; e) out+=E ;;
          f) out+=F ;; g) out+=G ;; h) out+=H ;; i) out+=I ;; j) out+=J ;;
          k) out+=K ;; l) out+=L ;; m) out+=M ;; n) out+=N ;; o) out+=O ;;
          p) out+=P ;; q) out+=Q ;; r) out+=R ;; s) out+=S ;; t) out+=T ;;
          u) out+=U ;; v) out+=V ;; w) out+=W ;; x) out+=X ;; y) out+=Y ;;
          z) out+=Z ;;
          *) out+="$c" ;;
        esac
        i=$((i + 1))
      done
      printf '%s' "$out"
      ;;
  esac
}

riscv_tool_candidates() {
  # usage: riscv_tool_candidates as  → prints candidate names one per line
  local tool="$1"
  printf 'riscv64-unknown-elf-%s\n' "$tool"
  printf 'riscv64-elf-%s\n' "$tool"
}

# Resolve one tool. Echoes absolute path on success; returns 1 on miss.
# Env override: RISCV_<TOOL> (e.g. RISCV_AS).
resolve_riscv_tool() {
  local tool="$1"
  local env_var="RISCV_$(_riscv_upper "$tool")"
  local from_env
  eval "from_env=\${$env_var:-}"
  local cand path
  if [[ -n "$from_env" ]]; then
    printf '%s\n' "$from_env"
    return 0
  fi
  while IFS= read -r cand; do
    if path="$(command -v "$cand" 2>/dev/null)"; then
      printf '%s\n' "$path"
      return 0
    fi
  done < <(riscv_tool_candidates "$tool")
  return 1
}

# If any of the named tools are missing, print a LOUD skip and return 1
# (caller should `exit 0`). On success, exports RISCV_RESOLVED_<TOOL>=path.
require_riscv_tools_or_skip() {
  local prog="$1"
  shift
  local tool cand tried path miss=0
  local -a missing=()
  for tool in "$@"; do
    if path="$(resolve_riscv_tool "$tool")"; then
      eval "export RISCV_RESOLVED_$(_riscv_upper "$tool")=\"\$path\""
    else
      missing+=("$tool")
      miss=1
    fi
  done
  if [[ "$miss" -eq 0 ]]; then
    return 0
  fi
  echo "${prog}: skipping — RISC-V toolchain not found (install to enable)." >&2
  for tool in "${missing[@]}"; do
    tried="\$RISCV_$(_riscv_upper "$tool")"
    while IFS= read -r cand; do
      tried="${tried} | ${cand}"
    done < <(riscv_tool_candidates "$tool")
    echo "${prog}:   missing ${tool}: tried ${tried}" >&2
  done
  return 1
}
