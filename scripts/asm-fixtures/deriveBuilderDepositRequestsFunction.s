derive_builder_deposit_requests:
  mv a4, a3; mv a3, a2; mv a2, a1; mv a1, a0
  la a0, builder_deposit_contract_addr
  j stage_system_call
