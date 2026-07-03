bv_mtx_committed_chunked_snapshot_upsert:
  li t0, 0                      # j = 0
.Lcscsu_loop:
  beq t0, a2, .Lcscsu_done
  slli t1, t0, 7; add t1, a1, t1   # src = live[j]
  li t2, 0                      # i = 0
.Lcscsu_scan:
  beq t2, a4, .Lcscsu_no_match
  slli t3, t2, 7; add t3, a3, t3   # entry = table[i]
  li t4, 0
.Lcscsu_addr_cmp:
  li t5, 20; beq t4, t5, .Lcscsu_slot_cmp
  add t5, a0, t4; lbu t5, 0(t5); add t6, t3, t4; lbu t6, 0(t6); bne t5, t6, .Lcscsu_next_entry
  addi t4, t4, 1; j .Lcscsu_addr_cmp
.Lcscsu_slot_cmp:
  ld t5, 32(t1);  ld t6, 32(t3);  bne t5, t6, .Lcscsu_next_entry
  ld t5, 40(t1);  ld t6, 40(t3);  bne t5, t6, .Lcscsu_next_entry
  ld t5, 48(t1);  ld t6, 48(t3);  bne t5, t6, .Lcscsu_next_entry
  ld t5, 56(t1);  ld t6, 56(t3);  bne t5, t6, .Lcscsu_next_entry
  j .Lcscsu_store_payload
.Lcscsu_next_entry:
  addi t2, t2, 1; j .Lcscsu_scan
.Lcscsu_no_match:
  bgeu a4, a5, .Lcscsu_overflow
  slli t3, a4, 7; add t3, a3, t3   # dst = table[count]
  sd zero, 0(t3); sd zero, 8(t3); sd zero, 16(t3); sd zero, 24(t3)
  li t4, 0
.Lcscsu_addr_copy:
  li t5, 20; beq t4, t5, .Lcscsu_store_payload_append
  add t5, a0, t4; lbu t6, 0(t5); add t5, t3, t4; sb t6, 0(t5); addi t4, t4, 1; j .Lcscsu_addr_copy
.Lcscsu_store_payload_append:
  addi a4, a4, 1
.Lcscsu_store_payload:
  ld t4, 32(t1);  sd t4, 32(t3);  ld t4, 40(t1);  sd t4, 40(t3)
  ld t4, 48(t1);  sd t4, 48(t3);  ld t4, 56(t1);  sd t4, 56(t3)
  ld t4, 64(t1);  sd t4, 64(t3);  ld t4, 72(t1);  sd t4, 72(t3)
  ld t4, 80(t1);  sd t4, 80(t3);  ld t4, 88(t1);  sd t4, 88(t3)
  ld t4, 96(t1);  sd t4, 96(t3);  ld t4, 104(t1); sd t4, 104(t3)
  ld t4, 112(t1); sd t4, 112(t3); ld t4, 120(t1); sd t4, 120(t3)
  addi t0, t0, 1; j .Lcscsu_loop
.Lcscsu_overflow:
  li t0, 1; sd t0, 0(a6); mv a0, a4; li a1, 1; ret
.Lcscsu_done:
  mv a0, a4; li a1, 0; ret
