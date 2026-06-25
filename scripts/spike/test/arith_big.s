.option norelax
.section .text
.globl _start
_start:
  la t0, params
  la t1, va; sd t1, 0(t0)
  la t1, vb; sd t1, 8(t0)
  la t1, vc; sd t1, 16(t0)
  la t1, vm; sd t1, 24(t0)
  la t1, vd; sd t1, 32(t0)
  la t0, params
  .4byte 0x8022a073        # csrrs x0,0x802,t0
  la t0, vd; la t1, vexp; li t2, 4
.Lck:
  ld t3, 0(t0); ld t4, 0(t1); bne t3,t4,.Lfail
  addi t0,t0,8; addi t1,t1,8; addi t2,t2,-1; bnez t2,.Lck
  la t0, tohost; li t1,1; sd t1,0(t0)
1: j 1b
.Lfail:
  la t0, tohost; li t1,3; sd t1,0(t0)
2: j 2b
.section .data
.align 8
va:
  .dword 0x8796a5b4c3d2e1f0
  .dword 0x0f1e2d3c4b5a6978
  .dword 0xfedcba9876543210
  .dword 0x123456789abcdef0

vb:
  .dword 0x293a4b5c6d7e8f90
  .dword 0xa1b2c3d4e5f60718
  .dword 0x123456789abcdef0
  .dword 0xfedcba9876543210

vc:
  .dword 0xffffffffffffffff
  .dword 0xffffffffffffffff
  .dword 0xffffffffffffffff
  .dword 0xffffffffffffffff

vm:
  .dword 0xfffffffefffffc2f
  .dword 0xffffffffffffffff
  .dword 0xffffffffffffffff
  .dword 0xffffffffffffffff

vexp:
  .dword 0xce26f93e020bc1d0
  .dword 0x084b9df6b023e7a5
  .dword 0xf7eb0d6ccd32b2e5
  .dword 0xe464a3b3d7bb4622

vd: .zero 32
params: .zero 40
.align 6
.globl tohost
tohost: .dword 0
.globl fromhost
fromhost: .dword 0
