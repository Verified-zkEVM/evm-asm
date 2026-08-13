# orphan-blocks-synthetic.s — deliberate orphan for check-orphan-blocks --self-test
# (#12259). The gate MUST report .Lorphan_dead; a green run that misses it is
# not a gate (lesson of #12236 / #12195).
.option norvc
.section .text
.globl orphan_synth_dirty
orphan_synth_dirty:
  li t0, 1
  # Unconditional jump over the dead block — nothing targets .Lorphan_dead.
  j .Lorphan_alive
.Lorphan_dead:
  # ORPHAN: no incoming edge (not entry, not fallthrough, not a branch target).
  la t0, cahsr_code_length
  ld t0, 0(t0)
  ret
.Lorphan_alive:
  li a0, 0
  ret

.globl cahsr_code_length
cahsr_code_length:
  ret
