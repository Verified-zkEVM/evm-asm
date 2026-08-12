record_message_value_transfer:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5
  beqz s3, .Lrmvt_done
  ld t0, 0(s2); ld t1, 8(s2); or t0, t0, t1; ld t1, 16(s2); or t0, t0, t1; ld t1, 24(s2); or t0, t0, t1; beqz t0, .Lrmvt_done
  mv a0, s4; mv a1, s2; la a2, message_value_transfer_sender_post; jal ra, u256_sub_be; bnez a0, .Lrmvt_done
  mv t0, s0; mv t1, s1; li t2, 20
.Lrmvt_self_cmp:
  beqz t2, .Lrmvt_self
  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lrmvt_recipient_pre
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lrmvt_self_cmp
.Lrmvt_self:
  la s5, message_value_transfer_sender_post
.Lrmvt_recipient_pre:
  mv a0, s5; mv a1, s2; la a2, message_value_transfer_recipient_post; jal ra, u256_add_be; bnez a0, .Lrmvt_done
  mv a0, s0; mv a1, s4; la a2, message_value_transfer_sender_post; li a3, 0; li a4, 0; jal ra, record_nonstorage_effect
  mv a0, s1; mv a1, s5; la a2, message_value_transfer_recipient_post; li a3, 0; li a4, 0; jal ra, record_nonstorage_effect
.Lrmvt_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 64
  ret
