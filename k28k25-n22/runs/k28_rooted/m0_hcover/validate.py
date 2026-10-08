#!/opt/homebrew/bin/python3.12
"""M0 step 3: validate a family's cover certificate WITHOUT the generator.
 1. the CNF on disk is byte-identical to the one rebuilt from (family, perms, blocker words)  [sha256]
 2. every LL permutation is a bijection of 0..k-1 preserving the degree cells
 3. blocker words are distinct, of length k(k-1)/2
 4. 'listed' blockers == the words of the named list files (re-parsed here), as sets, bijectively
 5. 'filter_iii' blockers: inequality (4) of LEMMAS_draft Section 4 recomputed from the word on the given U FAILS
    (LHS m*C(q,2)+rho*q > RHS sum_{i<j in U} (U^gen_ij - 1 - q_ij)) -> the class is excluded by filter (iii)
usage: validate.py TAG [TAG ...]   (TAG like k10_c073)"""
import hashlib, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import cnfgen


def fail_iii(word, k, degrees, U):
    g = cnfgen.graph_of(word, k)
    m = 21 - k
    idx = [i for i in range(k) if U >> i & 1]
    assert idx, 'empty U'
    h = [bin(g[i]).count('1') for i in range(k)]
    T = sum(degrees[i] - 1 - h[i] for i in idx)
    q, r = divmod(T, m)
    lhs = m * q * (q - 1) // 2 + r * q
    rhs = 0
    for a, i in enumerate(idx):
        for j in idx[a + 1:]:
            Ug = min(4, degrees[i] + degrees[j] - 15) if (g[i] >> j & 1) else 4
            rhs += Ug - 1 - bin(g[i] & g[j]).count('1')
    return lhs > rhs, lhs, rhs


def list_words(fn, k):
    out = []
    for line in open(os.path.join(RUNS, fn)):
        line = line.split('#')[0].strip()
        g = [0] * k
        if line:
            for e in line.split(','):
                a, b = (int(x) - 2 for x in e.split('-'))
                assert 0 <= a < b < k
                g[a] |= 1 << b; g[b] |= 1 << a
        out.append(cnfgen.word_of(g, k))
    return out


def validate(tag):
    d = os.path.join(HERE, 'data', tag)
    c = json.load(open(os.path.join(d, f'cert_{tag}.json')))
    fam = c['family']; k = fam['k']; comp = tuple(fam['comp'])
    degrees, caps, lo, hi = cnfgen.family_params(k, comp)
    assert tuple(fam['degrees']) == degrees and tuple(fam['window']) == (lo, hi) and tuple(fam['caps']) == caps
    E = k * (k - 1) // 2
    perms = [tuple(p) for p in c['perms']]
    assert all(cnfgen.is_cell_perm(p, degrees) for p in perms), 'non-cell-preserving permutation'
    words = [b['word'] for b in c['blockers']]
    assert all(len(w) == E and set(w) <= {'0', '1'} for w in words) and len(set(words)) == len(words)
    _, text = cnfgen.build_full(k, comp, perms, words, comments=[f"M0 H-only cover {tag}", f"census_gen sha256 {c['census_gen_sha256']}"])
    sha = hashlib.sha256(text.encode()).hexdigest()
    disk = hashlib.sha256(open(os.path.join(d, c['cnf']), 'rb').read()).hexdigest()
    assert sha == c['cnf_sha256'] == disk, 'CNF does not match its certificate'
    listed = sorted(b['word'] for b in c['blockers'] if b['kind'] == 'listed')
    for fn in c['list_files']:
        assert sorted(list_words(fn, k)) == listed, f'listed blockers != {fn}'
    nf = 0
    for b in c['blockers']:
        if b['kind'] == 'filter_iii':
            bad, lhs, rhs = fail_iii(b['word'], k, degrees, b['U'])
            assert bad and (lhs, rhs) == (b['lhs'], b['rhs']), ('filter witness does not fail', b)
            nf += 1
        else:
            assert b['kind'] == 'listed'
    assert nf + len(listed) == len(words)
    print(f"{tag}: OK  cnf sha {sha[:16]} == disk; {len(perms)} cell-preserving perms; {len(listed)} listed "
          f"blockers == {len(c['list_files'])} list file(s); {nf} filter-(iii) witnesses fail as claimed")
    return dict(tag=tag, perms=len(perms), listed=len(listed), filtered=nf)


if __name__ == '__main__':
    for t in sys.argv[1:]:
        validate(t)
