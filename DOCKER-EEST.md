# Running the EEST Stateless Test via Docker

## What the image contains

- Pre-built `stateless_guest.elf` (Lean-verified RISC-V ELF, built from this repo)
- `ziskemu` v0.16.0 (built from source; runs the RISC-V guest)
- EEST `zkevm@v0.4.0` fixtures baked in (~221 MB)
- All scripts under `scripts/`

The image lets third-party evaluators reproduce the conformance test run with a
single `docker run` — no Lean, Rust, or RISC-V toolchain needed locally.

## Pull and run (pre-built image)

```bash
# Full run, all fixtures, 2 parallel jobs (~7 GB RAM each)
docker run --rm ghcr.io/verified-zkevm/evm-asm:latest

# Bump to 4 jobs if you have ≥32 GB RAM
docker run --rm ghcr.io/verified-zkevm/evm-asm:latest \
  --all --jobs 4 --quiet-passes --no-build

# Focused subset (faster smoke check)
docker run --rm ghcr.io/verified-zkevm/evm-asm:latest \
  --filter random_statetest --limit 50 --jobs 2 --no-build
```

## Reproducing on a Hetzner VPS

Recommended instance: **CX52** (32 GB RAM, 8 vCPU, Ubuntu 24.04, ~€0.10/hr).
CX62 (48 GB) or AX52 (64 GB) let you use `--jobs 4` safely.

```bash
# 1. Provision the instance via hcloud CLI or Hetzner Cloud Console
#    (Ubuntu 24.04, CX52 or larger)

# 2. Install Docker
curl -fsSL https://get.docker.com | sh

# 3. Pull and run the image
docker pull ghcr.io/verified-zkevm/evm-asm:latest
docker run --rm ghcr.io/verified-zkevm/evm-asm:latest \
  --all --jobs 2 --quiet-passes --no-build \
  2>&1 | tee eest-results.txt

# 4. Review results
tail -30 eest-results.txt

# 5. Destroy the instance when done
```

Expected output (approximate, current pass rate):
```
==> RESULTS  total=NNN  full=NN  root=NN  succ=NN  tail=NN
             fail=NN  error=NN  budget=NN  FALSE_POS=0
```

`FALSE_POS=0` is the soundness gate — the prover never approves an invalid block.

## Building the image locally

```bash
# Standard build (slow: ~30 min Lean + ~15 min Rust)
docker build -t evm-asm-eest .

# With BuildKit layer caching (faster on re-builds)
DOCKER_BUILDKIT=1 docker build -t evm-asm-eest .

# Override zisk tag or fixture tag
docker build \
  --build-arg ZISK_TAG=v0.16.0 \
  --build-arg EEST_TAG=zkevm@v0.4.0 \
  -t evm-asm-eest .
```

## Known caveats

- **ziskemu RAM**: each parallel job uses ~7 GB RSS. Default is `--jobs 2` (14 GB
  total). Override with `--jobs N` to match your machine. On unpatched ziskemu
  at `--jobs 4`, a 32 GB machine is right at the limit; use CX62/AX52 if OOM.
- **binutils package**: `binutils-riscv64-unknown-elf` is the Ubuntu 24.04 package
  name. If the build fails on a different distro, try `gcc-riscv64-linux-gnu`.
- **ziskemu version**: The image uses v0.16.0 built from source. The locally
  tested binary includes a `lowmem-floatlibsplit` patch; the stock v0.16.0 from
  source might OOM at `--jobs 4` on 32 GB. Stick to `--jobs 2` to be safe.
- **Build time**: The first Docker build takes ~45–90 min. Subsequent builds with
  GHA layer cache (`type=gha`) skip the unchanged stages.

## Automated image builds (GitHub Actions)

The workflow at `.github/workflows/docker.yml` builds and pushes the image to
`ghcr.io/verified-zkevm/evm-asm` on:
- Manual dispatch (`workflow_dispatch`)
- Push of a `docker/*` tag (e.g. `git tag docker/2026-06-06 && git push --tags`)

Image tags produced:
- `ghcr.io/verified-zkevm/evm-asm:latest`
- `ghcr.io/verified-zkevm/evm-asm:zkevm-v0.4.0-<sha>`
