bv_mtx_committed_chunked_latest_value:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  bgtu a3, a4, .Lcschunk_overflow
  mv s0, a5                    # out value ptr
  mv s1, a6                    # recipient scratch
  mv s2, a7                    # LE slot scratch
  sd zero, 0(s1); sd zero, 8(s1); sd zero, 16(s1); sd zero, 24(s1)
  li t0, 0
.Lcschunk_rkey:
  li t1, 20; beq t0, t1, .Lcschunk_rkey_done
  add t2, a0, t0; lbu t3, 0(t2); add t2, s1, t0; sb t3, 0(t2); addi t0, t0, 1; j .Lcschunk_rkey
.Lcschunk_rkey_done:
  addi t0, a1, 31; mv t1, s2; li t2, 32
.Lcschunk_slot_rev:
  beqz t2, .Lcschunk_call
  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Lcschunk_slot_rev
.Lcschunk_call:
  mv a0, s1; mv a1, s2; mv a4, s0
  jal ra, exec_log_latest_value
  beqz a0, .Lcschunk_no_match
  li a0, 1; j .Lcschunk_ret
.Lcschunk_no_match:
  li a0, 0; j .Lcschunk_ret
.Lcschunk_overflow:
  li a0, 2
.Lcschunk_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
