#!/usr/bin/env python3
"""Check the campaign's central claim: no satisfying assignment has ever been found.

The whole result turns on this one fact. A single SAT would be a good 2-colouring of K22, would
make R(K2x8,K2x5) = 23, and would end the campaign the other way. So it deserves a check that does
not depend on a single bookkeeping path.

WHY MORE THAN THE LEDGER. A parent containing a SAT child FAILS by construction: `ok` requires
`not s`. And a split row is written only `if ok`. So until 2026-09-15 a counterexample would have
appeared in NO ledger at all -- it printed a warning to a box's stdout log, which is not synced to
this repo and does not outlive the box. split_certify now also writes SAT_FOUND.jsonl immediately
and fsyncs it. This script reads BOTH, so neither path alone has to be trusted.

Exits 0 only if every source agrees there is no SAT and at least one source was actually read.
Exits 1 if a SAT is found anywhere. Exits 2 if it could not check anything, because "I found no
SAT" and "I looked at nothing" must never produce the same exit code (CLAUDE.md rule 3).

Usage: python3 scripts/referee/check_no_sat.py [--dir runs/k28_rooted]
"""
import argparse, glob, json, os, sys

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dir', default='runs/k28_rooted')
    a = ap.parse_args()
    findings, rows, files = [], 0, 0

    # 1. every ledger row: rc 10 is SAT, and split rows carry a per-parent sat count
    for f in glob.glob(os.path.join(a.dir, 'ledger_*.jsonl')):
        files += 1
        for ln, line in enumerate(open(f), 1):
            try: r = json.loads(line)
            except Exception: continue
            rows += 1
            if r.get('rc') == 10:
                findings.append(f'{os.path.basename(f)}:{ln} rc=10 (SAT)')
            sp = r.get('split')
            if isinstance(sp, dict) and sp.get('sat'):
                findings.append(f'{os.path.basename(f)}:{ln} split.sat={sp["sat"]}')

    # 2. the dedicated record, which is the ONLY place a SAT inside a failed parent can appear
    satfile = os.path.join(a.dir, 'SAT_FOUND.jsonl')
    if os.path.exists(satfile):
        files += 1
        for ln, line in enumerate(open(satfile), 1):
            if line.strip():
                findings.append(f'SAT_FOUND.jsonl:{ln} {line.strip()[:160]}')

    # 3. the per-child model files. A leaf that solves SAT writes SAT_<tag>_<hidx>_<label>_<ts>.txt
    #    the MOMENT it is solved; SAT_FOUND.jsonl above is written only when the whole parent ends,
    #    which for a monster cube can be 40 hours later. Added 2026-09-22 in review: until then a SAT
    #    found on the laptop lane sat in this directory, unread by this script, until its parent ended.
    #    Remote hosts write theirs to their own ledger dirs; the endgame watcher checks those by ssh.
    for mf in sorted(glob.glob(os.path.join(a.dir, 'SAT_*.txt'))):
        findings.append(f'model file {os.path.basename(mf)}')
    if files == 0:
        print(f'FAIL: no ledgers and no SAT_FOUND.jsonl under {a.dir} -- CHECKED NOTHING')
        return 2
    if findings:
        print(f'*** SAT FOUND -- {len(findings)} record(s). This would REFUTE the refutation. ***')
        for x in findings[:20]:
            print('   ', x)
        return 1
    print(f'OK: no SAT in {rows:,} ledger rows across {files} file(s)')
    print(f'    SAT_FOUND.jsonl: {"present but empty" if os.path.exists(satfile) else "absent (none ever recorded)"}')
    print('    SAT_*.txt model files: none')
    print('    Note: box stdout logs are a third, independent witness and are not read here;')
    print('    grep them for "*** SAT" or "SAT FOUND" if you want a source this repo did not produce.')
    return 0

if __name__ == '__main__':
    sys.exit(main())
