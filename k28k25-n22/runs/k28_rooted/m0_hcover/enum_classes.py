#!/opt/homebrew/bin/python3.12
"""M0 step 1: enumerate a family's pre-filter-(iii) classes with the VERBATIM generator (scripts/astra/census_gen.py),
reproducing census()'s loop, and attach to every class removed by filter (iii) a witness subset U.
Cross-checks: class count == gen JSON 'before'; survivor words == words of the H_*.txt list (every list file of the
family, as sets, all equal); witness exists <=> subset_ok False.
usage: enum_classes.py K C8 C9 C10   -> classes_k{K}_c{C8}{C9}{C10}.json"""
import importlib.util, json, os, re, sys, glob, time
HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = os.path.abspath(os.path.join(HERE, '..'))
spec = importlib.util.spec_from_file_location('cg', os.path.join(HERE, '..', '..', '..', 'scripts', 'astra', 'census_gen.py'))
cg = importlib.util.module_from_spec(spec); spec.loader.exec_module(cg)
sys.path.insert(0, HERE)
import cnfgen


def witness(H, degrees, m):
    """First U (as bitmask, increasing order) violating (4); recomputed directly, not via subset_ok's DP."""
    k = len(H)
    h = [H[i].bit_count() for i in range(k)]
    def kij(i, j):
        e = H[i] >> j & 1
        U = min(4, degrees[i] + degrees[j] - 15) if e else 4
        return U - 1 - (H[i] & H[j]).bit_count()
    K = [[kij(i, j) if i != j else 0 for j in range(k)] for i in range(k)]
    for mask in range(1, 1 << k):
        idx = [i for i in range(k) if mask >> i & 1]
        T = sum(degrees[i] - 1 - h[i] for i in idx)
        q, r = divmod(T, m)
        lhs = m * q * (q - 1) // 2 + r * q
        rhs = sum(K[i][j] for a, i in enumerate(idx) for j in idx[a + 1:])
        if lhs > rhs:
            return mask, dict(T=T, q=q, rho=r, lhs=lhs, rhs=rhs)
    return None, None


def list_words(k, comp):
    tag = f"_r{k}_c{comp[0]}{comp[1]}{comp[2]}.txt"
    files = sorted(f for f in glob.glob(os.path.join(RUNS, 'H_*' + tag)) if re.fullmatch(r'H_\d+_\d+_\d+' + re.escape(tag), os.path.basename(f)))
    sets = []
    for f in files:
        ws = []
        for line in open(f):
            line = line.split('#')[0].strip()
            g = [0] * k
            if line:
                for e in line.split(','):
                    a, b = (int(x) - 2 for x in e.split('-'))
                    g[a] |= 1 << b; g[b] |= 1 << a
            ws.append(cnfgen.word_of(g, k))
        sets.append(ws)
    assert files, 'no list file for family'
    assert all(sorted(s) == sorted(sets[0]) for s in sets), 'list files of one family differ'
    assert len(set(sets[0])) == len(sets[0]), 'duplicate words in list'
    return files, sets[0]


def main():
    k, c8, c9, c10 = map(int, sys.argv[1:5]); comp = (c8, c9, c10)
    t0 = time.time()
    degrees, caps, lo, hi = cnfgen.family_params(k, comp)
    m = 21 - k
    seen = {}
    for h, weight in cg.degree_patterns(degrees, caps, lo, hi):
        for g in cg.realizations(h, degrees):
            word, H, aut = cg.canon(g, degrees)
            w = ''.join(map(str, word))
            if w in seen:
                continue
            assert cnfgen.word_of(H, k) == w
            seen[w] = (H, aut)
    files, lw = list_words(k, comp)
    gj = json.load(open(files[0].replace('/H_', '/gen_').replace('.txt', '.json')))
    assert gj['root'] == k and tuple(gj['composition']) == comp and tuple(gj['window']) == (lo, hi)
    assert len(seen) == gj['before'], (len(seen), gj['before'])
    classes, surv = [], []
    for w in sorted(seen):
        H, aut = seen[w]
        ok = cg.subset_ok(H, degrees, m)
        U, info = witness(H, degrees, m)
        assert (U is None) == ok, ('witness/subset_ok disagree', w)
        if ok:
            surv.append(w)
            classes.append(dict(word=w, kind='listed'))
        else:
            classes.append(dict(word=w, kind='filter_iii', U=U, **info))
    assert sorted(surv) == sorted(lw), 'survivors != list file'
    assert len(surv) == gj['count']
    out = dict(k=k, comp=comp, degrees=degrees, caps=caps, window=(lo, hi), m=m,
               before=len(seen), listed=len(surv), filtered=len(seen) - len(surv),
               list_files=[os.path.basename(f) for f in files], classes=classes, secs=round(time.time() - t0, 1))
    fn = os.path.join(HERE, 'data', f"classes_k{k}_c{c8}{c9}{c10}.json")
    os.makedirs(os.path.dirname(fn), exist_ok=True)
    json.dump(out, open(fn, 'w'))
    print(f"family k={k} comp={comp}: before={len(seen)} listed={len(surv)} filtered={len(seen)-len(surv)} "
          f"list_files={len(files)} secs={out['secs']}", flush=True)


if __name__ == '__main__':
    main()
