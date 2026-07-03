derive_consolidation_requests:
  mv a4, a3                    # out buffer -> a4
  mv a3, a2                    # block exec payload -> a3
  mv a2, a1                    # code len -> a2
  mv a1, a0                    # predeploy code ptr -> a1
  la a0, consolidation_request_predeploy_addr   # target addr -> a0
  j stage_system_call          # tail call: a0/a1/a2 carry body ptr/len/status to our caller
