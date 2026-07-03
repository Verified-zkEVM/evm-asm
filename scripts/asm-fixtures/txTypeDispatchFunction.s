tx_type_dispatch:
  beqz a1, .Ltd_fail
  lbu t0, 0(a0)
  li t1, 0xc0
  bgeu t0, t1, .Ltd_legacy
  li t1, 1
  beq t0, t1, .Ltd_t1
  li t1, 2
  beq t0, t1, .Ltd_t2
  li t1, 3
  beq t0, t1, .Ltd_t3
  li t1, 4
  beq t0, t1, .Ltd_t4
  j .Ltd_fail
.Ltd_legacy:
  sd zero, 0(a2)
  sd zero, 0(a3)
  li a0, 0
  ret
.Ltd_t1:
  li t0, 1
  sd t0, 0(a2)
  li t1, 1
  sd t1, 0(a3)
  li a0, 0
  ret
.Ltd_t2:
  li t0, 2
  sd t0, 0(a2)
  li t1, 1
  sd t1, 0(a3)
  li a0, 0
  ret
.Ltd_t3:
  li t0, 3
  sd t0, 0(a2)
  li t1, 1
  sd t1, 0(a3)
  li a0, 0
  ret
.Ltd_t4:
  li t0, 4
  sd t0, 0(a2)
  li t1, 1
  sd t1, 0(a3)
  li a0, 0
  ret
.Ltd_fail:
  sd zero, 0(a2)
  sd zero, 0(a3)
  li a0, 1
  ret
