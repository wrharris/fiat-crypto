#!/bin/sh
set -eu

clang++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fuse-ld=lld -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing -Da24_hex='0x3039' -Da24_val='12345' -Da_minus_two_over_four_array='{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x30,0x39}' -Dbitwidth='64' -Dlimb_weight_gaps_array='{64,64,64,64}' -Dmodulus_array='{0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xed}' -Dmodulus_bytes_val='32' -Dmodulus_limbs='4' -Dq_mpz='(1_mpz<<255) - (1_mpz<<4) - (1_mpz<<1) - 1' "$@"
