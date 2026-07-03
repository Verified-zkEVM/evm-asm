u256_from_u64_be:
  # Zero the high 24 bytes.
  sd zero,  0(a1)
  sd zero,  8(a1)
  sd zero, 16(a1)
  # Write the u64 in BE order at bytes 24..32.
  srli t0, a0, 56; sb t0, 24(a1)
  srli t0, a0, 48; sb t0, 25(a1)
  srli t0, a0, 40; sb t0, 26(a1)
  srli t0, a0, 32; sb t0, 27(a1)
  srli t0, a0, 24; sb t0, 28(a1)
  srli t0, a0, 16; sb t0, 29(a1)
  srli t0, a0,  8; sb t0, 30(a1)
                  sb a0, 31(a1)
  ret
