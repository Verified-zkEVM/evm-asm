# Soundness preconditions on the guest's inputs

This document records **assumptions the guest is entitled to make about its inputs**. They are not
implementation details: a caller that violates one is outside the specified interface, and the
guest's behaviour on such an input carries no soundness guarantee.

Each entry states the assumption, why the guest needs it, and what happens if it is broken.

---

## 1. The input blob's length must be padded to an 8-byte (dword) multiple

**Assumption.** The byte length of the input region supplied to the guest is a multiple of 8.

**Why the guest needs it.** The guest's memory logic operates at **8-byte (dword) granularity**.
Its loads, its scans and its bounds arithmetic are all expressed in dword units — RISC-V `ld`/`sd`
against 8-aligned addresses, scans that advance by 8, and lengths reasoned about as dword counts.
A guest built on that granularity cannot express a read that stops mid-dword, so it treats the
input as a sequence of dwords and expects the final dword to be whole.

**Consequence if broken.** A trailing partial dword makes the guest's final read extend past the
end of the supplied input. Whether that is observable depends entirely on the environment
underneath:

- **ziskemu** creates the input section sized to the actual input and therefore **panics**:
  `Mem::read() section not found for addr: … with width: 1`. The row terminates abnormally and
  produces **no verdict at all** — neither an accept nor a reject.
- **spike** does not report it. The same read is satisfied silently from its mapping, and the run
  completes normally.

So an unpadded input yields **an abnormal termination on one backend and a silent read of
unspecified bytes on another**. The silent case is the dangerous one, because it is the side that
produces a verdict.

**Note that nothing in the ELF constrains this.** `readelf -lW` on the guest shows no LOAD segment
covering the input region at all — the region is created entirely by the emulator from the input
file it is handed. `RegionMap`'s `INPUT` extent is a **guest-side constant describing what the
guest believes it may read**, and it is never expressed as an ELF declaration. There is therefore
no linker or loader check that can catch an unpadded input; the padding is part of the **trusted
interface**, not something the toolchain enforces.

**Obligations this places on callers.**

- **Producers of real inputs** must emit a dword-aligned blob length.
- **Test and fixture harnesses** must pad each input to an 8-byte multiple before handing it to
  the guest. An unpadded fixture measures nothing: on ziskemu it is an unscored row, and on spike
  it is a verdict computed partly from bytes the fixture never specified.

**Do not "fix" this by widening the guest's bounds.** The guest reasoning in dword units is
deliberate and pervasive; making a single consumer byte-exact would leave the granularity
assumption in place everywhere else while removing the one place it was visible.

---

*Written by **Claude Code** (coord agent) at the maintainer's direction. Placed in `docs/` to match
the existing convention (`docs/agents/…`, `docs/4ch8f-…`) rather than creating a second top-level
documentation directory.*
