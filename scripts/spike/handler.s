# M-mode trap handler installed by spike_run at HANDLER_ADDR; mtvec points here.
# Guest issues two ecalls: read_input (t0=0xF2) and halt (a7=93).
# Any non-ecall trap (fault) is recorded so the driver can report it.
# Debug area (in the 0x60000000 region):
#   0x60008000 halt flag: 1 = clean halt, 2 = fault
#   0x60008010 mcause   0x60008018 mtval   0x60008020 mepc   (on fault)
.option norelax
.option norvc
.section .text
.globl _handler
_handler:
  csrr t6, mcause
  li   t5, 11                # ecall from M-mode
  bne  t6, t5, .Lfault
  li   t6, 93
  beq  a7, t6, .Lhalt
  li   t6, 0xF2
  beq  t0, t6, .Lrdin
  # unknown ecall (e.g. write_output t0=0x10): skip it
  csrr t3, mepc
  addi t3, t3, 4
  csrw mepc, t3
  mret
.Lrdin:
  li   t5, 0x40000000        # INPUT_ADDR
  sd   t5, 0(a0)             # *a0 = input base
  ld   t4, 8(t5)             # length at INPUT_ADDR+8
  sd   t4, 0(a1)             # *a1 = length
  csrr t3, mepc
  addi t3, t3, 4
  csrw mepc, t3
  mret
.Lfault:
  li   t5, 0x60008010
  csrr t4, mcause
  sd   t4, 0(t5)
  li   t5, 0x60008018
  csrr t4, mtval
  sd   t4, 0(t5)
  li   t5, 0x60008020
  csrr t4, mepc
  sd   t4, 0(t5)
  li   t5, 0x60008000
  li   t4, 2                 # halt flag = 2 (fault)
  sd   t4, 0(t5)
.Lfspin:
  j    .Lfspin
.Lhalt:
  li   t5, 0x60008000        # halt flag = 1 (clean)
  li   t4, 1
  sd   t4, 0(t5)
.Lspin:
  j    .Lspin
