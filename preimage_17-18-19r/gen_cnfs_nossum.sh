#!/bin/bash

for i in {16..19}
do
    ./satencoding -A espresso -a preimage -t 0 -f sha256 -r ${i} > nossum_sha256_preimage_${i}r_0hash.cnf
done

./satencoding -A espresso -a preimage -t 0 -f sha256 -r 64 > nossum_sha256_preimage_64r_0hash.cnf
