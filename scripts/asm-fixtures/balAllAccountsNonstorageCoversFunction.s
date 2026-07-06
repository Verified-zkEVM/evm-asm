bal_all_accounts_nonstorage_covers:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)
  mv s0, a0                   # BAL section ptr
  mv s1, a1                   # BAL section len
  mv s2, a2                   # effect array base (SORTED, deduplicated agg)
  mv s3, a3                   # effect record count
  mv s4, a4                   # skip-list ptr
  mv s10, a5                  # skip-list count
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lc3cov_fail
  mv s5, a0                   # BAL account cursor
  mv s8, a1                   # BAL account end
  # bmvmx.5.5.7.3 step c: LINEARIZED via a matched-bitmap, removing the old O(BAL*agg) inner
  # BAL scan (the last O(N^2) barrier blocking the effect-log cap lift). The effect agg is now
  # SORTED + deduplicated (every caller routes through nonstorage_effect_aggregate), so:
  #   Phase 1: iterate BAL accounts ONCE; binary-search the sorted agg for each (O(log agg),
  #            mirrors the forward .Lc3ns_bs); on a hit, set covered[mid]=1.
  #   Phase 2: iterate agg entries ONCE; a net-changed non-skip effect with covered[j]==0 was
  #            reproduced by exec but is ENTIRELY ABSENT from the BAL -> reject.
  # Total O((BAL+agg)*log agg) instead of O(BAL*agg). covered[] is sized to nonstorageEffectLogCap
  # bytes and indexed by agg index, so it stays valid as the cap is lifted. Semantics are
  # byte-identical to the prior linear-scan covers.
  # --- Phase 0: clear covered[0..count) ---
  la t0, c3cov_covered; li t1, 0
.Lc3cov_clr:
  beq t1, s3, .Lc3cov_clrdone
  add t2, t0, t1; sb x0, 0(t2)
  addi t1, t1, 1; j .Lc3cov_clr
.Lc3cov_clrdone:
  # --- Phase 1: mark each agg entry that some BAL account's address binary-searches to ---
.Lc3cov_mloop:
  beq s5, s8, .Lc3cov_mdone
  mv a0, s5; mv a1, s8; jal ra, rlp_walk_next
  bnez a1, .Lc3cov_fail       # malformed BAL list -> reject
  mv s5, a0; sub s9, a0, a2; mv s6, a2   # AccountChanges ptr/len
  mv a0, s9; mv a1, s6; jal ra, rlp_walk_init
  bnez a2, .Lc3cov_fail       # malformed account -> reject
  jal ra, rlp_walk_next                              # item 0 = address
  bnez a1, .Lc3cov_fail       # malformed account -> reject
  li t2, 20; bne a2, t2, .Lc3cov_madv   # not 20B -> covers nothing
  sub s7, a0, a2              # BAL addr ptr (20B BE) = search target
  li t4, 0                                 # lo
  mv a3, s3                                # hi = effect count
.Lc3cov_bs:
  bgeu t4, a3, .Lc3cov_madv                # lo >= hi -> agg has no entry for this BAL account
  add a4, t4, a3; srli a4, a4, 1           # mid = (lo+hi)/2
  slli t5, a4, 7; slli t6, a4, 4; sub t5, t5, t6; add t5, s2, t5   # &agg[mid] (mid*112)
  li a6, 0
.Lc3cov_bscmp:
  li a7, 20; beq a6, a7, .Lc3cov_bsfound   # 20 bytes equal -> covered[mid]=1
  add a0, t5, a6; lbu a1, 0(a0)            # agg[mid].addr[a6]
  add a0, s7, a6; lbu a2, 0(a0)            # target.addr[a6]
  bltu a1, a2, .Lc3cov_bslo                # agg[mid] < target -> upper half
  bltu a2, a1, .Lc3cov_bshi                # agg[mid] > target -> lower half
  addi a6, a6, 1; j .Lc3cov_bscmp
.Lc3cov_bslo:
  addi t4, a4, 1; j .Lc3cov_bs             # lo = mid+1
.Lc3cov_bshi:
  mv a3, a4; j .Lc3cov_bs                  # hi = mid
.Lc3cov_bsfound:
  la t0, c3cov_covered; add t0, t0, a4; li t1, 1; sb t1, 0(t0)   # covered[mid] = 1
.Lc3cov_madv:
  j .Lc3cov_mloop
.Lc3cov_mdone:
  # --- Phase 2: every net-changed non-skip agg entry must be covered ---
  li s6, 0                    # effect index j
.Lc3cov_eloop:
  beq s6, s3, .Lc3cov_ok
  slli t0, s6, 7; slli t1, s6, 4; sub t0, t0, t1; add s7, s2, t0   # effect[j] ptr (j*112)
  # --- net change? balance (32B) or nonce (u64) ---
  addi t2, s7, 32; addi t3, s7, 64
  ld t4, 0(t2);  ld t5, 0(t3);  bne t4, t5, .Lc3cov_changed
  ld t4, 8(t2);  ld t5, 8(t3);  bne t4, t5, .Lc3cov_changed
  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lc3cov_changed
  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lc3cov_changed
  ld t4, 96(s7); ld t5, 104(s7); bne t4, t5, .Lc3cov_changed
  j .Lc3cov_enext             # no net change -> no obligation
.Lc3cov_changed:
  # --- skip gas/value-coupled accounts {sender,recipient,coinbase} (gas-path checked) ---
  li t4, 0                                 # skip-list entry index
.Lc3cov_skloop:
  beq t4, s10, .Lc3cov_check               # not in skip-list -> must be present in BAL
  slli t5, t4, 5; add t5, s4, t5           # skip entry ptr (32B strided)
  li t6, 0
.Lc3cov_skcmp:
  li a0, 20; beq t6, a0, .Lc3cov_enext     # effect addr equals a skip entry -> skip
  add a0, s7, t6; lbu a1, 0(a0)            # effect addr byte
  add a0, t5, t6; lbu a2, 0(a0)            # skip entry byte
  bne a1, a2, .Lc3cov_skadv
  addi t6, t6, 1; j .Lc3cov_skcmp
.Lc3cov_skadv:
  addi t4, t4, 1; j .Lc3cov_skloop
.Lc3cov_check:
  la t0, c3cov_covered; add t0, t0, s6; lbu t1, 0(t0)
  beqz t1, .Lc3cov_fail       # net-changed non-skip exec effect absent from BAL -> reject
.Lc3cov_enext:
  addi s6, s6, 1; j .Lc3cov_eloop
.Lc3cov_ok:
  li a0, 0; j .Lc3cov_ret
.Lc3cov_fail:
  li a0, 1
.Lc3cov_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)
  addi sp, sp, 96
  ret
