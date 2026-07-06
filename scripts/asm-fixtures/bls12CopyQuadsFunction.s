blsf_copy_quads:
.Lblsf_cq_loop:
  beqz a2, .Lblsf_cq_done
  ld t0, 0(a0)
  sd t0, 0(a1)
  addi a0, a0, 8
  addi a1, a1, 8
  addi a2, a2, -1
  j .Lblsf_cq_loop
.Lblsf_cq_done:
  ret
