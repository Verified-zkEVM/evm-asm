.section .text
.globl _start
_start:
  # build operands (4*u64 LE each); only limb0 set, rest zero (bss-zeroed)
  la t0, va; li t1, 7;  sd t1, 0(t0)
  la t0, vb; li t1, 11; sd t1, 0(t0)
  la t0, vc; li t1, 5;  sd t1, 0(t0)
  la t0, vm; li t1, 20; sd t1, 0(t0)
  # param struct = 5 pointers {a,b,c,m,d}
  la t0, params
  la t1, va; sd t1, 0(t0)
  la t1, vb; sd t1, 8(t0)
  la t1, vc; sd t1, 16(t0)
  la t1, vm; sd t1, 24(t0)
  la t1, vd; sd t1, 32(t0)
  la t0, params
  .4byte 0x8022a073        # csrrs x0, 0x802, t0  -> arith256_mod
  # check vd limb0 == 2, limbs1..3 == 0
  la t0, vd
  ld t2, 0(t0); li t3, 2; bne t2, t3, .Lfail
  ld t2, 8(t0); bnez t2, .Lfail
  ld t2, 16(t0); bnez t2, .Lfail
  ld t2, 24(t0); bnez t2, .Lfail
  la t0, tohost; li t1, 1; sd t1, 0(t0)
1: j 1b
.Lfail:
  la t0, tohost; li t1, 3; sd t1, 0(t0)
2: j 2b
.section .data
.align 8
va: .zero 32
vb: .zero 32
vc: .zero 32
vm: .zero 32
vd: .zero 32
params: .zero 40
.align 6
.globl tohost
tohost: .dword 0
.globl fromhost
fromhost: .dword 0
