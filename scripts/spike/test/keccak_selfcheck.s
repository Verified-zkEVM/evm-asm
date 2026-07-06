.section .text
.globl _start
_start:
  la a0, state
  .4byte 0x80052073        # csrrs x0, 0x800, a0 -> Keccak-f[1600] in place
  # check lane0 == 0xF1258F7940E1DDE7
  ld   t2, 0(a0)
  li   t3, 0xF1258F7940E1DDE7
  bne  t2, t3, .Lfail
  # check lane1 == 0x84D5CCF933C0478A
  ld   t2, 8(a0)
  li   t3, 0x84D5CCF933C0478A
  bne  t2, t3, .Lfail
  # pass: tohost = 1  (exit code 0)
  la   t0, tohost; li t1, 1; sd t1, 0(t0)
1: j 1b
.Lfail:
  la   t0, tohost; li t1, 3; sd t1, 0(t0)   # exit code 1
2: j 2b
.section .data
.align 6
state:  .zero 200
.align 6
.globl tohost
tohost: .dword 0
.globl fromhost
fromhost: .dword 0
