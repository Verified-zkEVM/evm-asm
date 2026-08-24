bal_rlp_measure_into_throwaway:
  addi sp, sp, -16; sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a1
  mv a1, a2; mv a2, a3; mv a3, a4
  jalr ra, 0(s0)
  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16
  ret
