log_data_gas:
  li t0, 375; mul t1, a0, t0        # 375 * num_topics
  add t1, t1, t0                    # + LOG base (375)
  li t2, 8; mul t2, a1, t2          # 8 * data_bytes
  add a0, t1, t2
  ret
