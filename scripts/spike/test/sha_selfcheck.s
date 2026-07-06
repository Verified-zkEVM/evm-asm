.option norelax
.section .text
.globl _start
_start:
  # state = SHA-256 IV (8 u32 packed into 4 u64, little-endian host layout)
  la t0, sstate
  li t1, 0xbb67ae856a09e667; sd t1, 0(t0)
  li t1, 0xa54ff53a3c6ef372; sd t1, 8(t0)
  li t1, 0x9b05688c510e527f; sd t1, 16(t0)
  li t1, 0x5be0cd191f83d9ab; sd t1, 24(t0)
  # input = padded "abc" block (64 bytes); raw bytes 61 62 63 80 .. len=0x18 at end
  la t0, sinput
  li t1, 0x0000000080636261; sd t1, 0(t0)   # bytes: 61 62 63 80 00 00 00 00
  sd zero, 8(t0); sd zero,16(t0); sd zero,24(t0); sd zero,32(t0); sd zero,40(t0); sd zero,48(t0)
  li t1, 0x1800000000000000; sd t1, 56(t0)   # BE length 0x18 in last 8 bytes
  # param = {state_ptr, input_ptr}
  la t0, sparams
  la t1, sstate; sd t1, 0(t0)
  la t1, sinput; sd t1, 8(t0)
  la a0, sparams
  .4byte 0x80552073        # csrrs x0, 0x805, a0 -> sha256 compress
  # check sstate u64[0] == 0x8f01cfeaba7816bf (digest words ba7816bf,8f01cfea)
  la t0, sstate
  ld t2, 0(t0); li t3, 0x8f01cfeaba7816bf; bne t2, t3, .Lfail
  ld t2, 8(t0); li t3, 0x5dae2223414140de; bne t2, t3, .Lfail
  la t0, tohost; li t1, 1; sd t1, 0(t0)
1: j 1b
.Lfail:
  la t0, tohost; li t1, 3; sd t1, 0(t0)
2: j 2b
.section .data
.align 8
sstate:  .zero 32
sinput:  .zero 64
sparams: .zero 16
.align 6
.globl tohost
tohost: .dword 0
.globl fromhost
fromhost: .dword 0
