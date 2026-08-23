#!/usr/bin/env bash
# Install everything the reproduction scripts need, on a bare Debian/Ubuntu machine.
#
#   bash tools/provision.sh          # tiers 1 and 2 (certificates)
#   bash tools/provision.sh --lean   # also tier 3 (rebuild the Lean theorem)
#
# Then:
#   bash k35k25-lb22/verify.sh              # tier 1: seconds, python only
#   bash k34k33-n19/reconstruct.sh          # tier 2: ~2.4 CPU-hours
#   bash k34k33-n19/lean/rebuild.sh         # tier 3: hours, needs 64 GB RAM
#
# Everything is built from source into ~/ramsey-tools and added to PATH via
# ~/ramsey-tools/env.sh. Nothing is installed into /tmp: tools there vanish on reboot,
# and a missing solver makes the scripts produce zero proofs while exiting 0.
set -uo pipefail
WANT_LEAN=0; [ "${1:-}" = "--lean" ] && WANT_LEAN=1
T="$HOME/ramsey-tools"; mkdir -p "$T"
log(){ echo "[provision] $*"; }

log "system packages"
sudo apt-get update -qq
sudo apt-get install -y -qq build-essential git curl python3 xz-utils >/dev/null

# ---- CaDiCaL ---------------------------------------------------------------------------
# Version 3+ must be run with --no-factor, which the reproduction scripts pass: factoring
# introduces extension variables that the LRAT checker soundly rejects.
if [ ! -x "$T/bin/cadical" ]; then
  log "building CaDiCaL"
  rm -rf "$T/src/cadical"; mkdir -p "$T/src"
  git clone -q --depth 1 https://github.com/arminbiere/cadical "$T/src/cadical"
  ( cd "$T/src/cadical" && ./configure >/dev/null && make -j"$(nproc)" >/dev/null 2>&1 )
  mkdir -p "$T/bin" && cp "$T/src/cadical/build/cadical" "$T/bin/"
fi

# ---- lrat-trim -------------------------------------------------------------------------
if [ ! -x "$T/bin/lrat-trim" ]; then
  log "building lrat-trim"
  rm -rf "$T/src/lrat-trim"
  git clone -q --depth 1 https://github.com/arminbiere/lrat-trim "$T/src/lrat-trim"
  ( cd "$T/src/lrat-trim" && ./configure >/dev/null 2>&1 && make -j"$(nproc)" >/dev/null 2>&1 )
  cp "$T/src/lrat-trim/lrat-trim" "$T/bin/"
fi

# ---- lrat-check (from drat-trim) -------------------------------------------------------
# NOTE it prints "c VERIFIED" FOURTH FROM LAST, and a bare `grep VERIFIED` also matches
# "NOT VERIFIED". The reproduction scripts anchor on "^c VERIFIED" for that reason.
if [ ! -x "$T/bin/lrat-check" ]; then
  log "building lrat-check"
  rm -rf "$T/src/drat-trim"
  git clone -q --depth 1 https://github.com/marijnheule/drat-trim "$T/src/drat-trim"
  ( cd "$T/src/drat-trim" && make lrat-check >/dev/null 2>&1 )
  cp "$T/src/drat-trim/lrat-check" "$T/bin/"
fi

# ---- Lean, only for tier 3 -------------------------------------------------------------
if [ "$WANT_LEAN" = 1 ]; then
  if [ ! -x "$HOME/.elan/bin/lake" ]; then
    log "installing elan + Lean"
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain leanprover/lean4:v4.30.0 >/dev/null 2>&1
  fi
fi

cat > "$T/env.sh" <<ENV
export PATH="$T/bin:\$HOME/.elan/bin:\$PATH"
ENV
# shellcheck disable=SC1090
. "$T/env.sh"

log "verifying"
ok=1
for t in cadical lrat-trim lrat-check python3; do
  if command -v "$t" >/dev/null; then printf '  %-12s %s\n' "$t" "$(command -v "$t")"
  else printf '  %-12s MISSING\n' "$t"; ok=0; fi
done
printf '  %-12s %s\n' "cadical ver" "$(cadical --version 2>/dev/null)"
if [ "$WANT_LEAN" = 1 ]; then
  if command -v lake >/dev/null; then printf '  %-12s %s\n' "lake" "$(lake --version 2>&1 | head -1)"
  else printf '  %-12s MISSING\n' lake; ok=0; fi
  m=$(free -g | awk 'NR==2{print $2}')
  printf '  %-12s %s GB\n' "RAM" "$m"
  [ "$m" -lt 48 ] && echo "  WARNING: composing the Lean theorem imports ~16 GB of .olean at once."\
                          " It succeeded on 64 GB and failed on 16 GB."
fi
echo
[ "$ok" = 1 ] && echo "[provision] ready. run:  . $T/env.sh" \
              || { echo "[provision] INCOMPLETE"; exit 1; }
