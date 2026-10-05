# verbatim from Astra (GPT-6 via codex exec), round 4, 2026-09-09; runs/astra_round4_2026-09-09.md
from itertools import combinations, combinations_with_replacement, product
from functools import lru_cache
from math import factorial
from collections import Counter

def pairs(n):
    return tuple(combinations(range(n), 2))

def canon(g, colours):
    """Returns lex-min row-major word, canonical graph, and automorphism order."""
    n = len(g)
    cells = tuple(tuple(i for i in range(n) if colours[i] == d)
                  for d in sorted(set(colours)))
    def visit(cs):
        if not cs:
            return (), (), 1
        choices = []
        for v in cs[0]:
            rest = tuple(tuple(u for u in c if u != v) for c in cs)
            row = ()
            refined = []
            for c in rest:
                z = tuple(u for u in c if not (g[v] >> u) & 1)
                o = tuple(u for u in c if (g[v] >> u) & 1)
                row += (0,) * len(z) + (1,) * len(o)
                refined.extend(s for s in (z, o) if s)
            choices.append((row, v, tuple(refined)))
        least = min(x[0] for x in choices)
        best, lab, aut = None, None, 0
        used = []
        for row, v, refined in choices:
            if row != least:
                continue
            twin = next((u for u in used
                         if (g[u] ^ g[v]) & ~((1 << u) | (1 << v)) == 0), None)
            if twin is not None:
                continue
            used.append(v)
            mult = sum(1 for rr, u, cc in choices if rr == least and
                       (g[u] ^ g[v]) & ~((1 << u) | (1 << v)) == 0)
            tail, p, count = visit(refined)
            word = row + tail
            if best is None or word < best:
                best, lab, aut = word, (v,) + p, mult * count
            elif word == best:
                aut += mult * count
        return best, lab, aut
    word, p, aut = visit(cells)
    out = tuple(sum(((g[p[i]] >> p[j]) & 1) << j for j in range(n))
                for i in range(n))
    return word, out, aut

def graphical(ds):
    ds = sorted(ds, reverse=True)
    if any(d < 0 or d >= len(ds) for d in ds) or sum(ds) % 2:
        return False
    return all(sum(ds[:r]) <= r*(r-1) + sum(min(r, d) for d in ds[r:])
               for r in range(1, len(ds)+1))

def realizations(h, colours):
    """Covers all isomorphism types; duplicates are allowed."""
    n = len(h)
    def rec(v, g, rem):
        if v == n:
            yield g
            return
        groups = {}
        for u in range(v+1, n):
            if rem[u]:
                key = (colours[u], h[u], g[u] & ((1 << v)-1))
                groups.setdefault(key, []).append(u)
        groups = tuple(groups.values())
        def selections(j, need, picked):
            if j == len(groups):
                if need == 0:
                    yield picked
                return
            cell = groups[j]
            for r in range(min(len(cell), need)+1):
                yield from selections(j+1, need-r,
                                      picked + tuple(cell[len(cell)-r:]))
        if rem[v] < 0:
            return
        for nb in selections(0, rem[v], ()):
            rr = list(rem)
            gg = list(g)
            rr[v] = 0
            for u in nb:
                rr[u] -= 1
                gg[v] |= 1 << u
                gg[u] |= 1 << v
            if graphical(rr[v+1:]):
                yield from rec(v+1, tuple(gg), tuple(rr))
    yield from rec(0, (0,)*n, h)

def degree_patterns(colours, caps, lo, hi):
    classes = tuple(sorted(set(colours)))
    lists = [tuple(combinations_with_replacement(
             range(caps[colours.index(d)]+1), colours.count(d))) for d in classes]
    for blocks in product(*lists):
        h = sum(blocks, ())
        if sum(h) % 2 or not 2*lo <= sum(h) <= 2*hi or not graphical(h):
            continue
        weight = 1
        for block in blocks:
            weight *= factorial(len(block))
            for multiplicity in Counter(block).values():
                weight //= factorial(multiplicity)
        yield h, weight

def labelled_count(h):
    @lru_cache(None)
    def F(ds):
        if not ds:
            return 1
        if not graphical(ds):
            return 0
        r, tail = ds[0], ds[1:]
        answer = 0
        for nb in combinations(range(len(tail)), r):
            chosen = set(nb)
            answer += F(tuple(sorted(
                (d-(j in chosen) for j, d in enumerate(tail)), reverse=True)))
        return answer
    return F(tuple(sorted(h, reverse=True)))

def interval(d, e, edge):
    budget = min((d-9)**2+3, (e-9)**2+3)
    if edge:
        return max(0, d+e-15-budget), min(4, d+e-15)
    return max(0, 4-budget), min(4, d+e-13)

def subset_ok(g, degrees, m, tight88=False):
    n = len(g)
    col = [degrees[i]-1-g[i].bit_count() for i in range(n)]
    cap = [[0]*n for _ in range(n)]
    for i, j in pairs(n):
        edge = (g[i] >> j) & 1
        upper = interval(degrees[i], degrees[j], edge)[1]
        if not edge and not tight88:
            upper = 4
        cap[i][j] = cap[j][i] = upper-1-(g[i] & g[j]).bit_count()
    ts, ks = [0]*(1 << n), [0]*(1 << n)
    for mask in range(1, 1 << n):
        bit = mask & -mask
        i = bit.bit_length()-1
        rest = mask ^ bit
        ts[mask] = ts[rest]+col[i]
        ks[mask] = ks[rest]+sum(cap[i][j] for j in range(n) if rest >> j & 1)
        a, b = divmod(ts[mask], m)
        if m*a*(a-1)//2+b*a > ks[mask]:
            return False
    return True

def row_profiles(wcounts, k, total):
    """Each profile is ((number of rows of sum 0,...,4),...) for W8,W9,W10."""
    def cell_profiles(number, low, high):
        def rec(s, left, acc):
            if s == 5:
                if left == 0:
                    yield acc
                return
            for count in range(left+1) if low <= s <= high else (0,):
                yield from rec(s+1, left-count, acc+(count,))
        return tuple(rec(0, number, ()))
    options = [cell_profiles(wcounts[d-8], *interval(k, d, 0))
               for d in (8, 9, 10)]
    return tuple(p for p in product(*options)
                 if sum(s*p[d][s] for d in range(3) for s in range(5)) == total)

def census(hist, k, comp, tight88=False):
    hist, comp = tuple(hist), tuple(comp)
    assert len(hist) == len(comp) == 3 and sum(hist) == 22
    assert k in (8, 9, 10) and hist[k-8] > 0 and sum(comp) == k
    assert all(0 <= comp[i] <= hist[i]-(k == i+8) for i in range(3))
    degrees = sum(((d,)*comp[d-8] for d in (8, 9, 10)), ())
    w = tuple(hist[i]-(k == i+8)-comp[i] for i in range(3))
    S, m = sum(degrees), 21-k
    lo = max(0, -(-(S+3*k-84)//2))
    hi = min(k*(k-1)//2, (S+k*(k-15))//2)
    caps = tuple(min(4, k+d-15) for d in degrees)
    group_order = factorial(comp[0])*factorial(comp[1])*factorial(comp[2])
    seen, records, recurrence, orbit = set(), [], 0, 0
    for h, weight in degree_patterns(degrees, caps, lo, hi):
        recurrence += weight*labelled_count(h)
        for g in realizations(h, degrees):
            word, H, aut = canon(g, degrees)
            if word in seen:
                continue
            seen.add(word)
            orbit += group_order//aut
            if not subset_ok(H, degrees, m, tight88):
                continue
            t = sum(x.bit_count() for x in H)//2
            col = tuple(degrees[i]-1-H[i].bit_count() for i in range(k))
            records.append(dict(word=''.join(map(str, word)),
                edges=tuple((i+2, j+2) for i, j in pairs(k) if H[i] >> j & 1),
                aut=aut, t=t, columns=col, W=w,
                profiles=row_profiles(w, k, sum(col)),
                neighbour_intervals=tuple(interval(k, d, 1) for d in degrees)))
    assert recurrence == orbit, (recurrence, orbit)
    records.sort(key=lambda r: r['word'])
    return dict(hist=hist, root=k, composition=comp, window=(lo, hi),
                before=len(seen), F=recurrence, orbit=orbit,
                count=len(records), cubes=records)

def compositions(hist, k):
    return tuple((i, j, k-i-j)
        for i in range(k+1) for j in range(k-i+1)
        if all(0 <= x <= hist[d]-(k == d+8)
               for d, x in enumerate((i, j, k-i-j))))

def histograms():
    return tuple((a, 22-a-c, c) for a in range(8)
                 for c in range(11) if a % 2 == c % 2)

def totals(tight88=False):
    cache, out = {}, []
    for hist in histograms():
        k = 8 if hist[0] else (10 if hist == (0,20,2) else 9)
        count = 0
        for comp in compositions(hist, k):
            key = (k, comp)
            if key not in cache:
                cache[key] = census(hist, k, comp, tight88)['count']
            count += cache[key]
        out.append((hist, k, count))
    return tuple(out)

if __name__ == '__main__':
    import json, sys
    if sys.argv[1:] == ['--all']:
        answer = totals()
    else:
        a, b, c, k, i, j, l = map(int, sys.argv[1:])
        answer = census((a,b,c), k, (i,j,l))
    print(json.dumps(answer, indent=2))
