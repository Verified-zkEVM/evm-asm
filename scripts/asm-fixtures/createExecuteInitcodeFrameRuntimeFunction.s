create_execute_initcode_frame:
  la t0, create_child_status
  li t1, 4
  sd t1, 0(t0)
  la t0, create_child_return_len
  sd zero, 0(t0)
  la t0, create_child_code_len
  sd zero, 0(t0)
  la t0, create_child_returndata
  la t1, create_child_code
  li t2, 256
.Lcreate_exec_zero_loop:
  sb zero, 0(t0)
  sb zero, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  bnez t2, .Lcreate_exec_zero_loop
  li t0, 0
  la t2, create_child_initcode
  la t3, create_child_stack
  li t4, 0
  li t5, 1024
  la t1, create_child_init_len
  ld t1, 0(t1)
.Lcreate_exec_loop:
  beqz t5, .Lcreate_exec_oog
  addi t5, t5, -1
  bgeu t0, t1, .Lcreate_exec_stop
  add a0, t2, t0
  lbu t6, 0(a0)
  addi t0, t0, 1
  beqz t6, .Lcreate_exec_stop
  li a0, 0xf3
  beq t6, a0, .Lcreate_exec_return
  li a0, 0xfd
  beq t6, a0, .Lcreate_exec_revert
  li a0, 0xfe
  beq t6, a0, .Lcreate_exec_fail
  li a0, 0x52
  beq t6, a0, .Lcreate_exec_mstore
  li a0, 0x53
  beq t6, a0, .Lcreate_exec_mstore8
  li a0, 0x5f
  beq t6, a0, .Lcreate_exec_push0
  li a0, 0x60
  bltu t6, a0, .Lcreate_exec_fail
  li a0, 0x80
  bgeu t6, a0, .Lcreate_exec_fail
  j .Lcreate_exec_pushn
.Lcreate_exec_push0:
  li a1, 0
  j .Lcreate_exec_push_value
.Lcreate_exec_pushn:
  addi a2, t6, -0x5f
  add a3, t0, a2
  bltu t1, a3, .Lcreate_exec_fail
  li a1, 0
.Lcreate_exec_pushn_loop:
  beqz a2, .Lcreate_exec_push_value
  add a3, t2, t0
  lbu a4, 0(a3)
  addi t0, t0, 1
  li a3, 8
  bltu a3, a2, .Lcreate_exec_pushn_high
  slli a1, a1, 8
  or a1, a1, a4
  addi a2, a2, -1
  j .Lcreate_exec_pushn_loop
.Lcreate_exec_pushn_high:
  bnez a4, .Lcreate_exec_fail
  addi a2, a2, -1
  j .Lcreate_exec_pushn_loop
.Lcreate_exec_push_value:
  li a0, 16
  bgeu t4, a0, .Lcreate_exec_fail
  slli a0, t4, 3
  add a0, t3, a0
  sd a1, 0(a0)
  addi t4, t4, 1
  j .Lcreate_exec_loop
.Lcreate_exec_mstore:
  li a0, 2
  bltu t4, a0, .Lcreate_exec_fail
  addi t4, t4, -1
  slli a0, t4, 3
  add a0, t3, a0
  ld a1, 0(a0)
  addi t4, t4, -1
  slli a0, t4, 3
  add a0, t3, a0
  ld a2, 0(a0)
  li a0, 224
  bltu a0, a1, .Lcreate_exec_fail
  la a3, create_child_returndata
  add a3, a3, a1
  li a4, 24
.Lcreate_exec_mstore_zero_loop:
  sb zero, 0(a3)
  addi a3, a3, 1
  addi a4, a4, -1
  bnez a4, .Lcreate_exec_mstore_zero_loop
  li a4, 56
.Lcreate_exec_mstore_value_loop:
  srl a5, a2, a4
  sb a5, 0(a3)
  addi a3, a3, 1
  addi a4, a4, -8
  bgez a4, .Lcreate_exec_mstore_value_loop
  j .Lcreate_exec_loop
.Lcreate_exec_mstore8:
  li a0, 2
  bltu t4, a0, .Lcreate_exec_fail
  addi t4, t4, -1
  slli a0, t4, 3
  add a0, t3, a0
  ld a1, 0(a0)
  addi t4, t4, -1
  slli a0, t4, 3
  add a0, t3, a0
  ld a2, 0(a0)
  li a0, 255
  bltu a0, a1, .Lcreate_exec_fail
  la a3, create_child_returndata
  add a3, a3, a1
  sb a2, 0(a3)
  j .Lcreate_exec_loop
.Lcreate_exec_return:
  li a6, 2
  la a7, create_child_code_len
  la a5, create_child_code
  j .Lcreate_exec_finish_copy
.Lcreate_exec_revert:
  li a6, 3
  la a7, create_child_return_len
  la a5, create_child_returndata
  j .Lcreate_exec_finish_copy
.Lcreate_exec_finish_copy:
  li a0, 2
  bltu t4, a0, .Lcreate_exec_fail
  addi t4, t4, -1
  slli a0, t4, 3
  add a0, t3, a0
  ld a1, 0(a0)
  addi t4, t4, -1
  slli a0, t4, 3
  add a0, t3, a0
  ld a2, 0(a0)
  li a0, 256
  bltu a0, a2, .Lcreate_exec_fail
  add a0, a1, a2
  bltu a0, a1, .Lcreate_exec_fail
  li a3, 256
  bltu a3, a0, .Lcreate_exec_fail
  sd a2, 0(a7)
  beqz a2, .Lcreate_exec_set_status
  la a3, create_child_returndata
  add a3, a3, a1
  mv a4, a2
.Lcreate_exec_copy_result_loop:
  lbu a0, 0(a3)
  sb a0, 0(a5)
  addi a3, a3, 1
  addi a5, a5, 1
  addi a4, a4, -1
  bnez a4, .Lcreate_exec_copy_result_loop
  j .Lcreate_exec_set_status
.Lcreate_exec_stop:
  li a6, 2
.Lcreate_exec_set_status:
  li a0, 2
  bne a6, a0, .Lcreate_exec_store_status
  la a1, create_child_returndata
  li a2, 256
.Lcreate_exec_clear_return_buffer_loop:
  sb zero, 0(a1)
  addi a1, a1, 1
  addi a2, a2, -1
  bnez a2, .Lcreate_exec_clear_return_buffer_loop
.Lcreate_exec_store_status:
  la a0, create_child_status
  sd a6, 0(a0)
  li a0, 0
  ret
.Lcreate_exec_oog:
  la a0, create_child_status
  li a1, 5
  sd a1, 0(a0)
  li a0, 5
  ret
.Lcreate_exec_fail:
  la a0, create_child_status
  li a1, 4
  sd a1, 0(a0)
  li a0, 4
  ret
