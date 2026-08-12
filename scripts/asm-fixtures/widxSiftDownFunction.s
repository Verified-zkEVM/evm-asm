widx_sift_down:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # root
  mv s1, a1                  # heap count
.Lwidx_sift_loop:
  slli s2, s0, 1
  addi s2, s2, 1             # left child
  bgeu s2, s1, .Lwidx_sift_ret
  mv s3, s0                  # best index
  mv a0, s3; jal ra, widx_record_ptr; mv s4, a0
  mv a0, s2; jal ra, widx_record_ptr; mv s5, a0
  mv a0, s4; mv a1, s5; jal ra, widx_cmp32
  li t0, 0; bne a0, t0, .Lwidx_left_done
  mv s3, s2
.Lwidx_left_done:
  addi s6, s2, 1             # right child
  bgeu s6, s1, .Lwidx_choose_done
  mv a0, s3; jal ra, widx_record_ptr; mv s4, a0
  mv a0, s6; jal ra, widx_record_ptr; mv s5, a0
  mv a0, s4; mv a1, s5; jal ra, widx_cmp32
  li t0, 0; bne a0, t0, .Lwidx_choose_done
  mv s3, s6
.Lwidx_choose_done:
  beq s3, s0, .Lwidx_sift_ret
  mv a0, s0; jal ra, widx_record_ptr; mv s4, a0
  mv a0, s3; jal ra, widx_record_ptr; mv s5, a0
  mv a0, s4; mv a1, s5; jal ra, widx_swap_records
  mv s0, s3
  j .Lwidx_sift_loop
.Lwidx_sift_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
