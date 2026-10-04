#!/bin/bash
set -u
cd "${WORKSPACE:?set WORKSPACE to the Comparator workspace}"
export PATH=$HOME/.elan/bin:$HOME/cmp/lean4export/.lake/build/bin:$HOME/cmp/nanoda_lib/target/release:$HOME/go/bin:$PATH
echo "=== deps $(date -u +%T) ==="
nice -n 5 lake build Sbsound.Witness21Kernel Sbsound.BipBridge LRATCatcher.ComparatorUnsatK35K25 2>&1 | grep -E "error|depends on|Build completed|✖" -A3 | head -12
echo "DEPS_RC=${PIPESTATUS[0]}"
for cfg in faithful-k35k25 faithful-value-k35k25; do
  echo "=== comparator $cfg $(date -u +%T) ==="
  /usr/bin/time -v nice -n 5 lake env $HOME/cmp/comparator/.lake/build/bin/comparator Comparator/$cfg.json > Comparator/$cfg.log 2>&1
  echo "CMP_RC[$cfg]=$?"
  grep -E "Exporting|kernel accepts|okay|rror|Maximum resident|Elapsed" Comparator/$cfg.log | cut -c1-400
done
echo "=== ALL DONE $(date -u +%T) ==="
