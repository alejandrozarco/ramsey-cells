#!/bin/bash
set -u
cd /mnt/ssd/faithful_cmp/lean-sb
export PATH=$HOME/.elan/bin:$HOME/cmp/lean4export/.lake/build/bin:$HOME/cmp/nanoda_lib/target/release:$HOME/go/bin:$PATH
echo "=== deps $(date -u +%T) ==="
nice -n 5 lake build Sbsound.Witness18Kernel 2>&1 | grep -E "error|depends on|Build completed|✖" -A3 | head -12
echo "DEPS_RC=${PIPESTATUS[0]}"
for cfg in faithful-value-kernel faithful-k19; do
  echo "=== comparator $cfg $(date -u +%T) ==="
  nice -n 5 lake env $HOME/cmp/comparator/.lake/build/bin/comparator Comparator/$cfg.json > Comparator/$cfg.run2.log 2>&1
  echo "CMP_RC[$cfg]=$?"
  grep -E "Exporting|kernel accepts|okay|rror" Comparator/$cfg.run2.log | cut -c1-400
done
echo "=== ALL DONE $(date -u +%T) ==="
