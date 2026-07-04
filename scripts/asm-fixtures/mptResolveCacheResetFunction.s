mpt_resolve_cache_reset:
  la t0, mset_res_cache_valid
  li t1, 4096
.Lmrc_reset_loop:
  beqz t1, .Lmrc_reset_done
  sd zero, 0(t0)
  addi t0, t0, 8
  addi t1, t1, -1
  j .Lmrc_reset_loop
.Lmrc_reset_done:
  ret
