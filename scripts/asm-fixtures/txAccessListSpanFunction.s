tx_access_list_span:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # tx ptr
  mv s1, a1                   # tx len
  mv s2, a2                   # span ptr out
  mv s3, a3                   # span len out
  sd zero, 0(s2); sd zero, 0(s3)
  mv a0, s0; mv a1, s1; la a2, txal_type; la a3, txal_inner_off
  jal ra, tx_type_dispatch
  bnez a0, .Ltxal_fail
  la t0, txal_type; ld s4, 0(t0)
  la t0, txal_inner_off; ld t1, 0(t0)
  beqz s4, .Ltxal_none
  add s5, s0, t1              # inner ptr
  sub s6, s1, t1              # inner len
  li t0, 1
  beq s4, t0, .Ltxal_type1
  li t0, 2
  beq s4, t0, .Ltxal_type2
  li t0, 3
  beq s4, t0, .Ltxal_type3
  li t0, 4
  beq s4, t0, .Ltxal_type4
  j .Ltxal_fail
.Ltxal_type1:
  mv a0, s5; mv a1, s6; la a2, txal_decode
  jal ra, tx_eip2930_decode
  bnez a0, .Ltxal_fail
  la t0, txal_decode; ld t1, 128(t0); ld t2, 136(t0)
  j .Ltxal_have_span
.Ltxal_type2:
  mv a0, s5; mv a1, s6; la a2, txal_decode
  jal ra, tx_eip1559_decode
  bnez a0, .Ltxal_fail
  la t0, txal_decode; ld t1, 160(t0); ld t2, 168(t0)
  j .Ltxal_have_span
.Ltxal_type3:
  mv a0, s5; mv a1, s6; la a2, txal_decode
  jal ra, tx_eip4844_decode
  bnez a0, .Ltxal_fail
  la t0, txal_decode; lwu t1, 152(t0); lwu t2, 156(t0)
  j .Ltxal_have_span
.Ltxal_type4:
  mv a0, s5; mv a1, s6; la a2, txal_decode
  jal ra, tx_eip7702_decode
  bnez a0, .Ltxal_fail
  la t0, txal_decode; lwu t1, 152(t0); lwu t2, 156(t0)
.Ltxal_have_span:
  add t3, s5, t1
  sd t3, 0(s2); sd t2, 0(s3)
  li a0, 0
  j .Ltxal_ret
.Ltxal_none:
  li a0, 1
  j .Ltxal_ret
.Ltxal_fail:
  sd zero, 0(s2); sd zero, 0(s3)
  li a0, 2
.Ltxal_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 80
  ret
