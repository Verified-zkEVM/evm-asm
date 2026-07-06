.section .text
.globl _start
_start:
  la a0, state
  .4byte 0x80052073        # csrrs x0, 0x800, a0  -> Keccak-f[1600] in place
  la t0, tohost
  li t1, 1
  sd t1, 0(t0)
1: j 1b
.section .data
.align 6
.globl begin_signature
begin_signature:
state:
  .zero 200                # 25 u64, all zero
.globl end_signature
end_signature:
.align 6
.globl tohost
tohost: .dword 0
.globl fromhost
fromhost: .dword 0
