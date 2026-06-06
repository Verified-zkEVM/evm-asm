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
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
    | sh -s -- -y --default-toolchain stable --profile minimal
ENV PATH="/root/.cargo/bin:$PATH"

RUN git clone --depth 1 --branch "${ZISK_TAG}" \
    https://github.com/0xPolygonHermez/zisk /zisk
WORKDIR /zisk
RUN cargo build --release -p ziskemu


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

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:$PATH"

WORKDIR /evm-asm
COPY . .

# Install pinned Lean toolchain, fetch precompiled Mathlib oleans, then build
RUN elan toolchain install "$(cat lean-toolchain)"
RUN lake exe cache get && lake build codegen

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
