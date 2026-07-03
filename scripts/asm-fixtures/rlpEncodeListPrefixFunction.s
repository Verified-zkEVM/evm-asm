rlp_encode_list_prefix:
  li t0, 56
  bgeu a0, t0, .Lrelp_long
  # Short list: prefix = 0xc0 + payload_length (1 byte).
  addi t1, a0, 0xc0
  sb t1, 0(a1)
  li t2, 1
  sd t2, 0(a2)
  li a0, 0
  ret
.Lrelp_long:
  # Long list: prefix = 0xf7 + bc, then bc-byte BE length.
  li t3, 1
  li t4, 0x100
  bltu a0, t4, .Lrelp_have_bc
  li t3, 2
  slli t4, t4, 8
  bltu a0, t4, .Lrelp_have_bc
  li t3, 3
  slli t4, t4, 8
  bltu a0, t4, .Lrelp_have_bc
  li t3, 4
  slli t4, t4, 8
  bltu a0, t4, .Lrelp_have_bc
  li t3, 5
  slli t4, t4, 8
  bltu a0, t4, .Lrelp_have_bc
  li t3, 6
  slli t4, t4, 8
  bltu a0, t4, .Lrelp_have_bc
  li t3, 7
  slli t4, t4, 8
  bltu a0, t4, .Lrelp_have_bc
  li t3, 8
.Lrelp_have_bc:
  addi t4, t3, 0xf7
  sb t4, 0(a1)
  mv t5, a1
  addi t5, t5, 1
  addi t4, t3, -1
.Lrelp_emit_be:
  bltz t4, .Lrelp_be_done
  slli t6, t4, 3
  srl t0, a0, t6
  sb t0, 0(t5)
  addi t5, t5, 1
  addi t4, t4, -1
  j .Lrelp_emit_be
.Lrelp_be_done:
  addi t5, t3, 1
  sd t5, 0(a2)
  li a0, 0
  ret
