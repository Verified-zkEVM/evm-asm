# Sail model dependency

The generated Sail RISC-V Lean model, its extraction configuration, provenance,
regeneration scripts, and executable-emulator validation moved to
[`Verified-zkEVM/riscv-zkvm`](https://github.com/Verified-zkEVM/riscv-zkvm).
EvmAsm consumes the tagged package declared in `lakefile.toml` and imports its
stable `RiscvZkvm.Sail` library from `EvmAsm/Rv64/SailEquiv/StateRel.lean`.

`rv64im-instructions.txt` remains here because it is EvmAsm's coverage inventory
for the zkVM target, rather than an input to the Sail extraction.

To update the model, follow `riscv-zkvm/docs/maintenance.md`, publish a release
with `riscv-zkvm-oleans.tar.gz`, and only then update EvmAsm's tag and manifest.
