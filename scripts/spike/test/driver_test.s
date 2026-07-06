.section .text
.globl _start
_start:
  la a0, base_out
  la a1, len_out
  li t0, 0xF2
  ecall                     # read_input -> handler writes base->[a0], len->[a1]
  # write marker 0xAB to OUTPUT_ADDR(0xa0010000), and the returned base to OUTPUT+8
  li t1, 0xa0010000
  li t2, 0xAB
  sb t2, 0(t1)
  ld t3, 0(a0)              # input base returned by read_input
  sd t3, 8(t1)
  ld t4, 0(a1)              # length returned
  sd t4, 16(t1)
  li a7, 93
  ecall                     # halt
1: j 1b
.section .data
base_out: .dword 0
len_out:  .dword 0
