stage_blockhash_m29:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  # #12057 aligned: u64 LE from a0+404 via LBU pack
  lbu s0, 404(a0)
  lbu t1, 405(a0); slli t1, t1, 8; or s0, s0, t1
  lbu t1, 406(a0); slli t1, t1, 16; or s0, s0, t1
  lbu t1, 407(a0); slli t1, t1, 24; or s0, s0, t1
  lbu t1, 408(a0); slli t1, t1, 32; or s0, s0, t1
  lbu t1, 409(a0); slli t1, t1, 40; or s0, s0, t1
  lbu t1, 410(a0); slli t1, t1, 48; or s0, s0, t1
  lbu t1, 411(a0); slli t1, t1, 56; or s0, s0, t1
  sd s0, 0(a4)                # *cur_out = cur
  mv s1, a1                   # headers ptr
  mv s2, a2                   # headers len
  mv s6, a3                   # output table base
  mv s3, a5                   # count_out ptr (a5 reused as call arg below)
  li t0, 256
  bgeu s0, t0, .Lsbm_wincap
  mv t0, s0
.Lsbm_wincap:
  mv s4, t0                   # s4 = window
  li s5, 0                    # s5 = count
.Lsbm_count:
  bgeu s5, s4, .Lsbm_count_done
  addi t0, s5, 1              # age = count + 1
  sub a0, s0, t0              # target = cur - age
  mv a1, s1; mv a2, s2
  la a3, m29_hash_tmp; la a4, m29_off_tmp; la a5, m29_len_tmp
  jal ra, blockhash_from_witness_headers
  bnez a0, .Lsbm_count_done   # first miss -> contiguous stop
  addi s5, s5, 1
  j .Lsbm_count
.Lsbm_count_done:
  sd s5, 0(s3)                # *count_out = count
  li s4, 1
.Lsbm_fill:
  bgtu s4, s5, .Lsbm_done     # age > count -> done
  sub a0, s0, s4              # target = cur - age
  mv a1, s1; mv a2, s2
  sub t0, s5, s4             # idx = count - age
  slli t0, t0, 5             # idx * 32
  add a3, s6, t0             # a3 = &block_hashes[idx]
  mv s3, a3                  # keep the slot ptr across the call (s3 dead after count store)
  la a4, m29_off_tmp; la a5, m29_len_tmp
  jal ra, blockhash_from_witness_headers
  mv t0, s3                  # lo ptr
  addi t1, s3, 31            # hi ptr
  li t2, 16                  # pair count
.Lsbm_rev:
  lbu t3, 0(t0); lbu t4, 0(t1)
  sb t4, 0(t0); sb t3, 0(t1)
  addi t0, t0, 1; addi t1, t1, -1
  addi t2, t2, -1; bnez t2, .Lsbm_rev
  addi s4, s4, 1
  j .Lsbm_fill
.Lsbm_done:
  li a0, 0
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
