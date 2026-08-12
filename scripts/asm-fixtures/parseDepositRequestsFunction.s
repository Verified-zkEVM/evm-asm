parse_deposit_requests:
  addi sp, sp, -56
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                    # record ptr
  mv s1, a1                    # remaining log count
  mv s2, a2                    # output cursor
  mv s3, a2                    # output base
  mv s4, a3                    # status out ptr
  sd zero, 0(s4)               # status = 0 (ok)
.Lpdr_loop:
  beqz s1, .Lpdr_done
  la t0, pdr_deposit_addr
  li t1, 20; li t2, 0
.Lpdr_addrcmp:
  beq t2, t1, .Lpdr_addr_ok
  add t3, s0, t2; lbu t4, 0(t3)
  add t3, t0, t2; lbu t5, 0(t3)
  bne t4, t5, .Lpdr_next       # address mismatch -> not a deposit log
  addi t2, t2, 1; j .Lpdr_addrcmp
.Lpdr_addr_ok:
  ld t0, 32(s0); beqz t0, .Lpdr_next   # topic_count == 0 -> skip
  la t0, pdr_deposit_sig
  li t1, 32; li t2, 0
.Lpdr_sigcmp:
  beq t2, t1, .Lpdr_sig_ok
  add t3, s0, t2; lbu t4, 40(t3)       # byte record+40+t2 (topic0)
  add t3, t0, t2; lbu t5, 0(t3)
  bne t4, t5, .Lpdr_next       # topic0 mismatch -> not a deposit event
  addi t2, t2, 1; j .Lpdr_sigcmp
.Lpdr_sig_ok:
  ld a1, 72(s0)                # data_len
  addi a0, s0, 80              # data ptr
  mv a2, s2                    # out cursor
  jal ra, extract_deposit_data
  bnez a0, .Lpdr_malformed     # deposit log with malformed data -> block invalid
  addi s2, s2, 192             # appended one 192-byte deposit body
.Lpdr_next:
  ld t0, 72(s0); addi t0, t0, 7; andi t0, t0, -8; addi t0, t0, 80   # stride = 80 + roundup8(data_len)
  add s0, s0, t0
  addi s1, s1, -1; j .Lpdr_loop
.Lpdr_malformed:
  li t0, 1; sd t0, 0(s4)       # status = 1; stop (spec asserts here)
.Lpdr_done:
  sub a0, s2, s3               # total deposit-request bytes written
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 56
  ret
