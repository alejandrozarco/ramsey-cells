#!/bin/bash
set -u
cd "${WORKSPACE:?set WORKSPACE to the Comparator workspace}"
export PATH=$HOME/.elan/bin:$HOME/cmp/lean4export/.lake/build/bin:$HOME/cmp/nanoda_lib/target/release:$HOME/go/bin:$PATH
echo "=== deps $(date -u +%T) ==="
nice -n 5 lake build Sbsound.Witness25Kernel Sbsound.Witness21bKernel Sbsound.Witness18bKernel Sbsound.BipBridge LRATCatcher.ComparatorUnsatK211K24 LRATCatcher.ComparatorUnsatK211K23 LRATCatcher.ComparatorUnsatK35K24 2>&1 | grep -E "error|Build completed|✖" -A3 | head -12
echo "DEPS_RC=${PIPESTATUS[0]}"
for cfg in "$@"; do
  avail=$(free -g | awk '/Mem:/{print $7}')
  echo "=== comparator $cfg $(date -u +%T) avail ${avail}G ==="
  /usr/bin/time -v nice -n 5 lake env $HOME/cmp/comparator/.lake/build/bin/comparator Comparator/$cfg.json > Comparator/$cfg.log 2>&1
  echo "CMP_RC[$cfg]=$?"
  grep -E "kernel accepts|okay|rror|Maximum resident|Elapsed" Comparator/$cfg.log | cut -c1-300
done
echo "=== ALL DONE $(date -u +%T) ==="
