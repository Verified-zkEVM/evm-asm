account_writes_is_absent:
  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0
.Lawis_tx_scan:
  bgeu t3, t1, .Lawis_block; slli t4, t3, 7; add t4, t2, t4; li t5, 20; mv t6, t4; mv t0, a0
.Lawis_tx_cmp:
  beqz t5, .Lawis_tx_hit; lbu a1, 0(t6); lbu a2, 0(t0); bne a1, a2, .Lawis_tx_next; addi t6, t6, 1; addi t0, t0, 1; addi t5, t5, -1; j .Lawis_tx_cmp
.Lawis_tx_next:
  addi t3, t3, 1; j .Lawis_tx_scan
.Lawis_tx_hit:
  ld t0, 112(t4); andi t0, t0, 8; beqz t0, .Lawis_no; ld t0, 72(t4); beqz t0, .Lawis_yes; j .Lawis_no
.Lawis_block:
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lawis_blk_scan:
  bgeu t3, t1, .Lawis_no; slli t4, t3, 7; add t4, t2, t4; li t5, 20; mv t6, t4; mv t0, a0
.Lawis_blk_cmp:
  beqz t5, .Lawis_blk_hit; lbu a1, 0(t6); lbu a2, 0(t0); bne a1, a2, .Lawis_blk_next; addi t6, t6, 1; addi t0, t0, 1; addi t5, t5, -1; j .Lawis_blk_cmp
.Lawis_blk_next:
  addi t3, t3, 1; j .Lawis_blk_scan
.Lawis_blk_hit:
  ld t0, 112(t4); andi t0, t0, 8; beqz t0, .Lawis_no; ld t0, 72(t4); beqz t0, .Lawis_yes
.Lawis_no:
  li a0, 0; ret
.Lawis_yes:
  li a0, 1; ret
