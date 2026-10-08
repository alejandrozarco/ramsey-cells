#!/usr/bin/env python3
"""M4: compare the Lean-printed cover CNFs with the M0 files and re-run cake_lpr on the Lean-printed files.

Inputs: cnf/<tag>.cnf printed by PrintCover.lean (no comment lines), m0_hcover/data/<tag>/cover_<tag>.cnf and
cover_<tag>.trim.lrat. For each family: sha256 of the Lean file, sha256 of the M0 file with its leading
comment lines removed, equality, and the cake_lpr verdict on (Lean file, M0 trimmed LRAT).
Writes cover_print_compare.jsonl and cakelpr_cover.jsonl (one row per family, timestamps from the system clock).
usage: check_cover_print.py"""
import glob, hashlib, json, os, subprocess, time

HERE = os.path.dirname(os.path.abspath(__file__))
M0 = os.path.join(HERE, '..', 'm0_hcover', 'data')
CAKE = os.path.expanduser('~/claude_projects/sat/cake_lpr/cake_wrap.sh')


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    cmp_rows, cake_rows = [], []
    for f in sorted(glob.glob(os.path.join(HERE, 'cnf', '*.cnf'))):
        tag = os.path.basename(f)[:-4]
        lean = open(f, 'rb').read()
        m0 = open(os.path.join(M0, tag, f'cover_{tag}.cnf'), 'rb').read()
        body = b''.join(l for l in m0.splitlines(keepends=True) if not l.startswith(b'c '))
        row = dict(tag=tag, lean_sha256=sha(lean), m0_body_sha256=sha(body), m0_file_sha256=sha(m0),
                   identical=(lean == body), lean_bytes=len(lean))
        cmp_rows.append(row)
        t0 = time.time()
        r = subprocess.run(['nice', '-n', '10', CAKE, f, os.path.join(M0, tag, f'cover_{tag}.trim.lrat')],
                           capture_output=True, text=True)
        out = (r.stdout + r.stderr).strip().splitlines()
        cake_rows.append(dict(tag=tag, cnf_sha256=row['lean_sha256'], rc=r.returncode,
                              verified=any('s VERIFIED UNSAT' in l for l in out),
                              last_line=out[-1] if out else '', secs=round(time.time() - t0, 2),
                              utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())))
        print(tag, row['identical'], cake_rows[-1]['verified'], flush=True)
    with open(os.path.join(HERE, 'cover_print_compare.jsonl'), 'w') as fh:
        for r in cmp_rows:
            fh.write(json.dumps(r) + '\n')
    with open(os.path.join(HERE, 'cakelpr_cover.jsonl'), 'w') as fh:
        for r in cake_rows:
            fh.write(json.dumps(r) + '\n')
    print('identical', sum(r['identical'] for r in cmp_rows), '/', len(cmp_rows),
          'verified', sum(r['verified'] for r in cake_rows), '/', len(cake_rows))


if __name__ == '__main__':
    main()
