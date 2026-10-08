#!/usr/bin/env python3
"""M5 step 1: the cube table.

For every census case (the 781 gen_<tag>.json lists) and every LISTED word of its M0 family certificate
(m0_hcover/data/<fam>/cert_<fam>.json, blockers of kind `listed`, in certificate order = the order of
`listedWords` in Lean), find the list-file line whose edge list equals `wordEdges k w` (row-major pairs
(i+2, j+2)) verbatim, and attach one cake_lpr verdict:

  direct  a ledger row with rc 20, cake_verified, cnf_sha256 and no `split`; option set from its
          `encoding` field, or for rows without one from m2_encoder/m6_match_*.jsonl (hash-matched by Lean)
  split   a ledger row with a `split` tree, rc 20, cake_verified, whose leaves (nodes without children)
          all carry cnf_sha256 + cake_verified and whose leaf literal lists form a complete case split
          (coversB, re-implemented here exactly as RootedBridge/Split.lean); option set = parent `encoding`
          with channel/wallpairs/auth forced on (split_certify.py)
  pending none of the above (yet)

Sources: the local ledgers runs/k28_rooted/ledger_*.jsonl and, if given, a read-only mirror of the arm-vm's
~/ramsey/regen/{ledgers,split_ledgers} (--mirror DIR, an rsync copy). Rows are de-duplicated by
their JSON text. A row only counts for the list (tag) it belongs to (census_grades.py rule; aliases as there).

Output (in this directory):
  cube_table.jsonl   one line per (case, listed-word index): tag, case key, widx, hidx, H, kind, option
                     set, recorded hash(es), source (file:line), alternates
  mirror_rows_used.jsonl  the mirror rows (raw) that supply an attached verdict, kept as evidence
  cases.json         the 781 cases (tag -> (n8, n9, n10, v8, v9, v10)), including the 125 with no cube
  table_summary.json counts, pending list, problems
usage: m5_table.py [--mirror DIR] [--resolve]
"""
import argparse, collections, glob, hashlib, json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.abspath(os.path.join(HERE, '..'))
M0 = os.path.join(D, 'm0_hcover', 'data')
ALIAS = {'0_22_0_root9_astra47_2M': '0_22_0_r9_c090', '0_22_0_root9_astra47_PROOF': '0_22_0_r9_c090',
         '0_22_0_astra47': '0_22_0_r9_c090'}

OPTS = {  # option-set names -> Lean Opts fields (tight always on; shortfall always off)
    'O1': dict(budget=True, channel=False, wallpairs=False, auth=False, base_codegree=True),
    'O1b': dict(budget=True, channel=False, wallpairs=False, auth=False, base_codegree=False),
    'O2': dict(budget=True, channel=True, wallpairs=True, auth=True, base_codegree=True),
    'O3': dict(budget=True, channel=True, wallpairs=True, auth=True, base_codegree=False),
}


def opt_name(enc, split=False):
    """Option-set name of a ledger `encoding` field (None if it is not one of OPTS)."""
    e = dict(enc)
    if e.get('shortfall'): return None
    if not e.get('budget', False): return None
    if split:
        e.update(channel=True, wallpairs=True, auth=True)
    d = dict(budget=True, channel=bool(e.get('channel', False)), wallpairs=bool(e.get('wallpairs', False)),
             auth=bool(e.get('auth', False)), base_codegree=bool(e.get('base_codegree', True)))
    for n, o in OPTS.items():
        if o == d: return n
    return None


def root_of(n8, n10):
    return 8 if n8 > 0 else (10 if n10 > 0 else 9)


def pairs(k):
    return [(i, j) for i in range(k) for j in range(k) if i < j]


def word_edges(k, word):
    return [(i + 2, j + 2) for n, (i, j) in enumerate(pairs(k)) if word[n] == '1']


def covers_b(n, us):
    """RootedBridge/Split.lean `coversB`, transcribed."""
    if n == 0: return False
    if any(len(u) == 0 for u in us): return True
    if not us or not us[0]: return False
    l = us[0][0]
    if l == 0: return False
    if not all(u[0] in (l, -l) for u in us): return False
    pos = [u[1:] for u in us if u[0] == l]
    neg = [u[1:] for u in us if u[0] == -l]
    return covers_b(n - 1, pos) and covers_b(n - 1, neg)


EXE = os.path.abspath(os.path.join(D, '..', '..', '..', 'lean', 'lrat-catcher', '.lake', 'build', 'bin', 'lratcatch-export-rooted'))
RESOLVE = os.path.join(HERE, 'opt_resolve.json')


def resolve_split_opt(case, hidx, H, leaf, cache):
    """Option set of a split row without `encoding`: print its first leaf with the Lean exporter
    (lrat-catcher, the M2 printer) under O3 and O2 and keep the one whose sha256 is the recorded one."""
    ck = f"{case['tag']}#{hidx}#{leaf[1]}"
    if ck in cache: return cache[ck]
    n8, n9, n10, v8, v9, v10 = case['key']
    degs = [8] * n8 + [9] * n9 + [10] * n10
    comp = [(d, v) for d, v in ((8, v8), (9, v9), (10, v10)) if v]
    hit = None
    for name in ('O3', 'O2'):
        o = OPTS[name]
        fd, out = tempfile.mkstemp(suffix='.cnf'); os.close(fd)
        job = '\t'.join([f'out={out}', 'N=22', 'colors=K2x8,K2x5', 'degs=' + ','.join(map(str, degs)),
                         f"root={case['k']}", 'comp=' + ','.join(f'{d}:{v}' for d, v in comp),
                         'H=' + ','.join(f'{a}-{b}' for a, b in H)]
                        + [f'{k}={int(v)}' for k, v in o.items()]
                        + ['units=' + ','.join(map(str, leaf[0])), f"childof={case['tag']} #{hidx}"])
        subprocess.run(['nice', '-n', '10', EXE, '-'], input=job + '\n', capture_output=True, text=True)
        h = hashlib.sha256(open(out, 'rb').read()).hexdigest() if os.path.getsize(out) else None
        os.unlink(out)
        if h == leaf[1]: hit = name; break
    cache[ck] = hit
    json.dump(cache, open(RESOLVE, 'w'), indent=0)
    return hit


def leaves(node):
    ch = node.get('children') or []
    if not ch:
        yield node
    for c in ch:
        yield from leaves(c)


def load_cases():
    cases = {}
    for f in sorted(glob.glob(f'{D}/gen_*_r*_c*.json')):
        tag = os.path.basename(f)[4:-5]
        g = json.load(open(f))
        n8, n9, n10 = g['hist']; v8, v9, v10 = g['composition']
        assert tuple(g.get('degrees', (8, 9, 10))) == (8, 9, 10)
        assert g['root'] == root_of(n8, n10), tag
        lines = [l.split('#')[0].strip() for l in open(f'{D}/H_{tag}.txt')]
        lines = [l for l in lines if l]
        H = [[tuple(int(x) for x in e.split('-')) for e in l.split(',')] for l in lines]
        cases[tag] = dict(tag=tag, key=(n8, n9, n10, v8, v9, v10), k=g['root'], lines=H)
    return cases


def load_certs():
    fams = {}
    for f in sorted(glob.glob(f'{M0}/*/cert_*.json')):
        c = json.load(open(f))
        k, comp = c['family']['k'], c['family']['comp']
        words = [b['word'] for b in c['blockers'] if b['kind'] == 'listed']
        fams[(k, comp[0], comp[1], comp[2])] = words
    return fams


def ledger_files(mirror):
    out = []
    for f in sorted(glob.glob(f'{D}/ledger_*.jsonl')):
        out.append(('local', f))
    if mirror:
        for sub in ('ledgers', 'split_ledgers'):
            for f in sorted(glob.glob(f'{mirror}/{sub}/ledger_*.jsonl')):
                out.append((f'arm-vm/{sub}', f))
    return out


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--mirror', default=None)
    ap.add_argument('--resolve', action='store_true', help='resolve the option set of split rows without encoding')
    a = ap.parse_args()
    cache = json.load(open(RESOLVE)) if os.path.exists(RESOLVE) else {}
    cases = load_cases(); fams = load_certs()
    m6 = {}
    for f in sorted(glob.glob(f'{D}/m2_encoder/m6_match_*.jsonl')):
        for l in open(f):
            r = json.loads(l)
            if r['match'] and r['match']['filtered']:
                m6[(r['tag'], r['line'])] = r['match']['variant']
    # ---- verdict candidates per (tag, sorted H)
    mirror_raw = {}
    seen = set(); direct = collections.defaultdict(list); split = collections.defaultdict(list)
    nrows = collections.Counter()
    for src, f in ledger_files(a.mirror):
        tag = os.path.basename(f)[7:-6]; tag = ALIAS.get(tag, tag)
        if tag not in cases: continue
        for ln, L in enumerate(open(f), 1):
            L = L.strip()
            if not L or L in seen: continue
            seen.add(L)
            try: r = json.loads(L)
            except Exception: continue
            if r.get('rc') != 20 or not r.get('cake_verified'): continue
            key = tuple(sorted(tuple(e) for e in r['H']))
            where = f'{os.path.relpath(f, D) if src == "local" else src + "/" + os.path.basename(f)}:{ln}'
            if src != 'local': mirror_raw[where] = L
            if 'split' in r:
                nrows['split rows'] += 1
                lv = list(x for c in r['split'].get('child_rows') or [] for x in leaves(c))
                ok = bool(lv) and all(x.get('cnf_sha256') and x.get('cake_verified') and x.get('literals') is not None
                                      for x in lv)
                o = opt_name(r['encoding'], split=True) if r.get('encoding') is not None else None
                split[(tag, key)].append(dict(src=where, opt=o, leaves_ok=ok,
                                              leaves=[(x['literals'], x.get('cnf_sha256')) for x in lv],
                                              checked_at=r.get('checked_at_utc'), host=r.get('host')))
            else:
                if not r.get('cnf_sha256'): continue
                nrows['direct rows'] += 1
                if r.get('encoding') is not None:
                    o = opt_name(r['encoding']); how = 'encoding'
                elif src == 'local' and (tag, ln) in m6:
                    o = m6[(tag, ln)]; how = 'm6_match'
                else:
                    o = None; how = 'unknown'
                direct[(tag, key)].append(dict(src=where, opt=o, how=how, sha=r['cnf_sha256'],
                                               checked_at=r.get('checked_at_utc'), host=r.get('host')))
    # ---- the table
    out = open(os.path.join(HERE, 'cube_table.jsonl'), 'w')
    used_src = set()
    tally = collections.Counter(); pending = []; problems = []
    nfam_words = 0
    for tag in sorted(cases):
        cs = cases[tag]; n8, n9, n10, v8, v9, v10 = cs['key']; k = cs['k']
        words = fams[(k, v8, v9, v10)]
        line_sets = [tuple(sorted(h)) for h in cs['lines']]
        used = set()
        for widx, w in enumerate(words):
            nfam_words += 1
            we = word_edges(k, w)
            hits = [i for i, h in enumerate(cs['lines']) if h == we]
            if not hits:
                problems.append(dict(tag=tag, widx=widx, problem='listed word not in list file verbatim',
                                     set_match=[i for i, s in enumerate(line_sets) if s == tuple(sorted(we))]))
                continue
            hidx = hits[0]; used.add(hidx)
            key = tuple(sorted(we))
            row = dict(tag=tag, key=cs['key'], k=k, widx=widx, hidx=hidx, H=we)
            dc = [d for d in direct.get((tag, key), []) if d['opt']]
            for s in split.get((tag, key), []):
                if s['leaves_ok'] and not s['opt'] and a.resolve and not direct.get((tag, key)):
                    s['opt'] = resolve_split_opt(cs, hidx, we, s['leaves'][0], cache)
                    if s['opt']: s['opt_from'] = 'resolved by Lean print of the first leaf'
            sc = [s for s in split.get((tag, key), []) if s['leaves_ok'] and s['opt']]
            for s in sc:
                us = [list(l) for l, _ in s['leaves']]
                s['fuel'] = max(len(u) for u in us) + 1
                s['covers'] = covers_b(s['fuel'], us)
            sc = [s for s in sc if s['covers']]
            if dc:
                # prefer rows whose option set came from the row itself, then the m6 match
                dc.sort(key=lambda d: (d['how'] != 'encoding',))
                row.update(kind='direct', opt=dc[0]['opt'], sha=dc[0]['sha'], src=dc[0]['src'],
                           alternates=[dict(opt=d['opt'], sha=d['sha'], src=d['src']) for d in dc[1:4]]
                           + [dict(split=s['src']) for s in sc[:1]])
            elif sc:
                s = sc[0]
                row.update(kind='split', opt=s['opt'], opt_from=s.get('opt_from', 'encoding'), src=s['src'], fuel=s['fuel'],
                           childof=f'{tag} #{hidx}', leaves=s['leaves'],
                           alternates=[dict(split=x['src']) for x in sc[1:3]])
            else:
                why = []
                if direct.get((tag, key)): why.append(f"{len(direct[(tag, key)])} cake direct row(s), option set unknown")
                if split.get((tag, key)):
                    why.append(f"{len(split[(tag, key)])} cake split row(s): " + '; '.join(
                        f"leaves_ok={s['leaves_ok']} opt={s['opt']} covers={s.get('covers')}" for s in split[(tag, key)]))
                row.update(kind='pending', opt='O2', why=why or ['no cake_lpr row'])
                pending.append(dict(tag=tag, hidx=hidx, widx=widx, H=we, why=row['why']))
            if row.get('src'): used_src.add(row['src'])
            tally[row['kind']] += 1
            tally[f"{row['kind']} {row['opt']}"] += 1
            out.write(json.dumps(row) + '\n')
        extra = [i for i in range(len(cs['lines'])) if i not in used]
        if extra:
            problems.append(dict(tag=tag, problem='list lines that are no listed word', hidx=extra))
        if len(set(line_sets)) != len(line_sets):
            problems.append(dict(tag=tag, problem='duplicate list lines'))
    out.close()
    used = sorted({r for r in used_src if r in mirror_raw})
    with open(os.path.join(HERE, 'mirror_rows_used.jsonl'), 'w') as fo:
        for w in used: fo.write(json.dumps({'src': w, 'row': json.loads(mirror_raw[w])}) + '\n')
    json.dump({t: c['key'] for t, c in sorted(cases.items())}, open(os.path.join(HERE, 'cases.json'), 'w'), indent=0)
    summ = dict(cases=len(cases), families=len(fams), listed_word_slots=nfam_words,
                list_lines=sum(len(c['lines']) for c in cases.values()), rows_seen=dict(nrows),
                tally=dict(sorted(tally.items())), pending=pending, problems=problems, mirror=a.mirror)
    json.dump(summ, open(os.path.join(HERE, 'table_summary.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in summ.items() if k not in ('pending', 'problems')}, indent=1))
    print(f'pending {len(pending)}  problems {len(problems)}')
    for p in problems[:20]: print('  PROBLEM', p)


if __name__ == '__main__':
    main()
