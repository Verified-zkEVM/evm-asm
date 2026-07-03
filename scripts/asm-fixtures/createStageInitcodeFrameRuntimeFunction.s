create_stage_initcode_frame:
  la t0, create_child_status
  sd zero, 0(t0)
  la t0, create_child_kind
  sd a2, 0(t0)
  la t0, create_child_return_len
  sd zero, 0(t0)
  la t0, create_child_code_len
  sd zero, 0(t0)
  la t0, create_init_size
  ld t1, 0(t0)
  la t2, create_child_init_len
  sd t1, 0(t2)
  la t0, create_sender_be
  la t2, create_child_creator_be
  li t3, 32
.Lcreate_stage_copy_creator:
  lbu t4, 0(t0)
  sb t4, 0(t2)
  addi t0, t0, 1
  addi t2, t2, 1
  addi t3, t3, -1
  bnez t3, .Lcreate_stage_copy_creator
  la t0, create_address_be
  la t2, create_child_target_be
  li t3, 32
.Lcreate_stage_copy_target:
  lbu t4, 0(t0)
  sb t4, 0(t2)
  addi t0, t0, 1
  addi t2, t2, 1
  addi t3, t3, -1
  bnez t3, .Lcreate_stage_copy_target
  addi t0, a1, 31
  la t2, create_child_value_be
  li t3, 32
.Lcreate_stage_copy_value:
  lbu t4, 0(t0)
  sb t4, 0(t2)
  addi t0, t0, -1
  addi t2, t2, 1
  addi t3, t3, -1
  bnez t3, .Lcreate_stage_copy_value
  la t0, create_init_offset
  ld t2, 0(t0)
  add t0, a0, t2
  la t2, create_child_initcode
  mv t3, t1
.Lcreate_stage_copy_initcode:
  beqz t3, .Lcreate_stage_done
  lbu t4, 0(t0)
  sb t4, 0(t2)
  addi t0, t0, 1
  addi t2, t2, 1
  addi t3, t3, -1
  j .Lcreate_stage_copy_initcode
.Lcreate_stage_done:
  la t0, create_child_status
  li t1, 1
  sd t1, 0(t0)
  li a0, 0
  ret
