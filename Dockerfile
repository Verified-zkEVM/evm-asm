# ── Stage 1: build ziskemu from source ───────────────────────────────────────
FROM ubuntu:24.04 AS ziskemu-builder

ARG ZISK_TAG=v0.16.0
ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    git curl ca-certificates build-essential cmake \
    libomp-dev libgmp-dev protobuf-compiler uuid-dev \
    nasm libclang-dev clang \
    libopenmpi-dev openmpi-bin \
    nlohmann-json3-dev \
    libgrpc++-dev libprotobuf-dev \
    libsecp256k1-dev libsodium-dev \
    libpqxx-dev \
    gcc-riscv64-unknown-elf \
    python3 \
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
    | sh -s -- -y --default-toolchain stable --profile minimal
ENV PATH="/root/.cargo/bin:$PATH"

RUN git clone --depth 1 --branch "${ZISK_TAG}" \
    https://github.com/0xPolygonHermez/zisk /zisk
WORKDIR /zisk
RUN cargo build --release -p ziskemu

# Collect zisk project licenses (dual MIT/Apache-2.0) and a per-crate license inventory
RUN mkdir -p /license-report \
    && for f in LICENSE LICENSE.md LICENSE.txt LICENSE-MIT LICENSE-APACHE \
                LICENCE LICENCE.md LICENCE-MIT LICENCE-APACHE COPYING; do \
         if [ -f "/zisk/$f" ]; then cp "/zisk/$f" "/license-report/zisk-${f}"; fi; \
       done \
    && cargo metadata --format-version 1 \
       | python3 -c 'import json,sys; [print(p["name"], p["version"], p.get("license") or "UNKNOWN") for p in sorted(json.load(sys.stdin)["packages"], key=lambda p: p["name"].lower())]' \
       > /license-report/zisk-rust-crates.txt


# ── Stage 2: Lean build + ELF emit + fixture bake ────────────────────────────
FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive
ARG EEST_TAG=zkevm@v0.4.0
ARG GIT_COMMIT=unknown
ARG GIT_REF=unknown
ARG BUILD_DATE=unknown

# gcc-riscv64-unknown-elf provides riscv64-unknown-elf-{as,ld,gcc}
RUN apt-get update && apt-get install -y --no-install-recommends \
    git curl ca-certificates python3 xxd \
    gcc-riscv64-unknown-elf binutils-riscv64-unknown-elf \
    && rm -rf /var/lib/apt/lists/*

COPY --from=ziskemu-builder /zisk/target/release/ziskemu /usr/local/bin/ziskemu

# Copy zisk/Rust license artifacts from builder stage
COPY --from=ziskemu-builder /license-report/ /usr/local/share/licenses/

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:$PATH"

WORKDIR /evm-asm
COPY . .

# Install pinned Lean toolchain, fetch precompiled Mathlib oleans, then build
RUN elan toolchain install "$(cat lean-toolchain)"
RUN lake exe cache get && lake build codegen

# Collect license files from each Lean package in .lake/packages/
RUN mkdir -p /usr/local/share/licenses/lean-packages \
    && for pkg_dir in .lake/packages/*/; do \
         pkg_name=$(basename "$pkg_dir"); \
         for f in LICENSE LICENSE.md LICENSE.txt NOTICE NOTICE.md COPYING; do \
           if [ -f "${pkg_dir}${f}" ]; then \
             cp "${pkg_dir}${f}" \
               "/usr/local/share/licenses/lean-packages/${pkg_name}-${f}"; \
             break; \
           fi; \
         done; \
       done

# Generate Ubuntu package inventory; copyright texts live in /usr/share/doc/<pkg>/copyright
RUN dpkg-query -W --showformat='${Package} ${Version}\n' \
    > /usr/local/share/licenses/ubuntu-packages.txt

# Fetch elan and EEST fixture top-level licenses; fall back to a URL pointer on failure
RUN curl -sSf \
      https://raw.githubusercontent.com/leanprover/elan/master/LICENSE \
      -o /usr/local/share/licenses/elan-LICENSE.txt \
    || printf 'elan: Apache-2.0\nhttps://github.com/leanprover/elan/blob/master/LICENSE\n' \
      > /usr/local/share/licenses/elan-LICENSE.txt
RUN curl -sSf \
      https://raw.githubusercontent.com/ethereum/execution-spec-tests/main/LICENSE \
      -o /usr/local/share/licenses/eest-LICENSE.txt \
    || printf 'execution-spec-tests: MIT\nhttps://github.com/ethereum/execution-spec-tests/blob/main/LICENSE\n' \
      > /usr/local/share/licenses/eest-LICENSE.txt

# Emit the stateless_guest RISC-V ELF (codegen appends .elf)
RUN lake exe codegen --program stateless_guest --halt linux93 \
    -o gen-out/stateless_guest

# Fetch and bake in EEST fixtures (~221 MB, no gh CLI needed; uses curl fallback)
RUN bash scripts/eest-fetch-fixtures.sh "${EEST_TAG}"

LABEL org.opencontainers.image.licenses="MIT"
LABEL org.opencontainers.image.source="https://github.com/Verified-zkEVM/evm-asm"
LABEL org.opencontainers.image.revision="${GIT_COMMIT}"
LABEL org.opencontainers.image.ref.name="${GIT_REF}"
LABEL org.opencontainers.image.created="${BUILD_DATE}"
LABEL eest.fixture.tag="${EEST_TAG}"

ENTRYPOINT ["bash", "scripts/codegen-eest-stateless-check.sh"]
# --jobs 2 keeps RSS under ~14 GB on a 32 GB host; bump to --jobs 4 on 64 GB+
CMD ["--all", "--jobs", "2", "--quiet-passes", "--no-build"]
