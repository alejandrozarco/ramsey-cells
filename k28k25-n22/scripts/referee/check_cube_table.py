#!/usr/bin/env python3
"""Check the M5 cube table (runs/k28_rooted/m5_final/cube_table.jsonl.gz) against the deposited list files and
ledgers, and summarise the hash binding (binding_verify.jsonl.gz). Reads only files in this directory tree.

1. Every line of the 781 list files H_<tag>.txt is exactly one table row (same tag, same edge list in the
   same order); 23,886 rows.
2. direct rows: the ledger row named by `src` (ledger_<tag>.jsonl:<line>) has the row's H (as a set),
   rc 20, cake_verified, no `split`, and cnf_sha256 == the table's `sha`.
3. split rows: the ledger row named by `src` has the row's H, rc 20, cake_verified and a split tree whose
   leaves (nodes without children) all carry cnf_sha256 and cake_verified; the table's (literals, sha256)
   leaf list equals that leaf list; the leaf literal lists form a complete case split (`coversB`, as in
   lean/sbsound/RootedBridge/Split.lean, with the table's `fuel`).
4. Where the ledger row has an `encoding` field, it names the table's option set (O1/O2/O3).
5. binding_verify: the last record of every (tag, hidx) is BOUND, with files == matched; total files.
usage: check_cube_table.py"""
import collections, gzip, json, os, sys

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'runs', 'k28_rooted')
M5 = os.path.join(D, 'm5_final')
OPTS = {'O1': (True, False, False, False, True), 'O2': (True, True, True, True, True),
        'O3': (True, True, True, True, False)}


def opt_name(enc, split):
    e = dict(enc)
    if e.get('shortfall') or not e.get('budget', False): return None
    if split: e.update(channel=True, wallpairs=True, auth=True)
    t = (True, bool(e.get('channel')), bool(e.get('wallpairs')), bool(e.get('auth')), bool(e.get('base_codegree', True)))
    return next((n for n, o in OPTS.items() if o == t), None)


def covers_b(n, us):
    if n == 0: return False
    if any(len(u) == 0 for u in us): return True
    if not us or not us[0]: return False
    l = us[0][0]
    if l == 0 or not all(u[0] in (l, -l) for u in us): return False
    return covers_b(n - 1, [u[1:] for u in us if u[0] == l]) and covers_b(n - 1, [u[1:] for u in us if u[0] == -l])


def leaves(node):
    ch = node.get('children') or []
    if not ch: yield node
    for c in ch: yield from leaves(c)


def main():
    rows = [json.loads(l) for l in gzip.open(os.path.join(M5, 'cube_table.jsonl.gz'), 'rt')]
    bad = collections.Counter(); ex = []
    def fail(kind, r, msg=''):
        bad[kind] += 1
        if len(ex) < 10: ex.append(f"{kind}: {r.get('tag')} #{r.get('hidx')} {msg}")
    lines = {}
    for r in rows:
        if r['tag'] not in lines:
            ls = [l.split('#')[0].strip() for l in open(os.path.join(D, f"H_{r['tag']}.txt"))]
            lines[r['tag']] = [[[int(x) for x in e.split('-')] for e in l.split(',')] for l in ls if l]
    seen = set()
    for r in rows:
        L = lines[r['tag']]
        if not (0 <= r['hidx'] < len(L)) or L[r['hidx']] != r['H']: fail('list line', r)
        if (r['tag'], r['hidx']) in seen: fail('duplicate', r)
        seen.add((r['tag'], r['hidx']))
    import glob
    for f in glob.glob(os.path.join(D, 'H_*_r*_c*.txt')):
        t = os.path.basename(f)[2:-4]
        n = sum(1 for l in open(f) if l.split('#')[0].strip())
        for i in range(n):
            if (t, i) not in seen: bad['list line without row'] += 1
    cache = {}
    kinds = collections.Counter(); nleaves = 0; enc_checked = 0
    for r in rows:
        f, ln = r['src'].rsplit(':', 1)
        if f not in cache: cache[f] = open(os.path.join(D, f)).read().split('\n')
        try: g = json.loads(cache[f][int(ln) - 1])
        except Exception: fail('src unreadable', r, r['src']); continue
        kinds[r['kind']] += 1
        if sorted(map(tuple, g['H'])) != sorted(map(tuple, r['H'])): fail('H', r)
        if g.get('rc') != 20 or not g.get('cake_verified'): fail('verdict', r)
        if g.get('encoding') is not None:
            enc_checked += 1
            if opt_name(g['encoding'], r['kind'] == 'split') != r['opt']: fail('option set', r)
        if r['kind'] == 'direct':
            if 'split' in g or g.get('cnf_sha256') != r['sha']: fail('direct hash', r)
        elif r['kind'] == 'split':
            lv = [x for c in (g.get('split') or {}).get('child_rows') or [] for x in leaves(c)]
            if not lv or not all(x.get('cnf_sha256') and x.get('cake_verified') for x in lv): fail('leaf verdict', r)
            if [[x.get('literals'), x.get('cnf_sha256')] for x in lv] != r['leaves']: fail('leaf list', r)
            if not covers_b(r['fuel'], [u for u, _ in r['leaves']]): fail('coversB', r)
            nleaves += len(r['leaves'])
        else:
            fail('kind', r, r['kind'])
    last = {}
    for l in gzip.open(os.path.join(M5, 'binding_verify.jsonl.gz'), 'rt'):
        v = json.loads(l); last[(v['tag'], v['hidx'])] = v
    nb = sum(1 for k in seen if k in last and last[k]['verdict'] == 'BOUND' and last[k]['files'] == last[k]['matched'])
    files = sum(last[k]['files'] for k in seen if k in last)
    print(f"rows {len(rows)} (list lines {sum(len(v) for v in lines.values())} in {len(lines)} non-empty lists); "
          f"direct {kinds['direct']}, split {kinds['split']} ({nleaves} leaves); option set checked against "
          f"`encoding` for {enc_checked} rows")
    print(f"binding: {nb}/{len(rows)} rows BOUND, {files} printed files")
    if bad or nb != len(rows):
        print('FAIL', dict(bad)); [print('  ', e) for e in ex]; sys.exit(1)
    print('OK: every list line has one table row whose ledger row is cake_lpr VERIFIED with the recorded hash(es)')


if __name__ == '__main__':
    main()
