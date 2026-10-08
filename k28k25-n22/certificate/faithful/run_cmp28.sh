#!/bin/bash
# M5 Comparator run on the Linux workstation (faithful-value-k28k25.json, nanoda enabled). Holds flock ~/lean.lock for the whole run,
# waits for MemAvailable >= 15 GB before starting, kills its own comparator if MemAvailable drops below 1 GB.
# Writes cmp.log (transcript), cmp.rc, DONE. Usage (detached): setsid nohup bash run_cmp28.sh WORKSPACE OUTDIR &
set -u
WS=${1:?workspace}; OUT=${2:?outdir}; mkdir -p "$OUT"
exec 9> "$HOME/lean.lock"; flock 9
export PATH=$HOME/.elan/bin:$HOME/cmp/lean4export/.lake/build/bin:$HOME/cmp/nanoda_lib/target/release:$HOME/go/bin:$PATH
until [ "$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)" -ge 15 ]; do echo "$(date -u +%T) waiting for memory" >> "$OUT/wait.log"; sleep 300; done
cd "$WS"
echo "start $(date -u +%FT%TZ)" > "$OUT/cmp.meta"
( /usr/bin/time -v nice -n 19 lake env "$HOME/cmp/comparator/.lake/build/bin/comparator" Comparator/k28k25/faithful-value-k28k25.json > "$OUT/cmp.log" 2>&1; echo $? > "$OUT/cmp.rc" ) &
CP=$!
while kill -0 $CP 2>/dev/null; do
  if [ "$(awk '/MemAvailable/{print int($2/1024)}' /proc/meminfo)" -lt 1024 ]; then
    echo "$(date -u +%T) MemAvailable < 1 GB: stopping comparator" >> "$OUT/cmp.meta"
    pkill -P $CP; for p in $(pgrep -f "comparator/.lake/build/bin/comparator Comparator/k28k25"); do pkill -P $p; kill $p; done
  fi
  sleep 20
done
echo "end $(date -u +%FT%TZ)" >> "$OUT/cmp.meta"
touch "$OUT/DONE"
