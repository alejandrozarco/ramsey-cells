# verbatim from Astra (GPT-6 via codex exec), round 12b, 2026-09-09: independent checker of the census lists (obligation G).
# Source: runs/astra_round12b_2026-09-09.md. Second enumeration for root-8 families; count certificate for k = 9, 10.
#!/usr/bin/env python3
"""Independent obligation-G checker; Python >=3.10, standard library only."""
import argparse
import hashlib
import importlib.util
import itertools as it
import json
import math
import re
import sys
import time
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path

sys.dont_write_bytecode = True


def require(ok, message):
    if not ok:
        raise ValueError(message)


def graph(k, edges):
    g = [0] * k
    for u, v in edges:
        require(type(u) is int and type(v) is int, "noninteger endpoint")
        require(0 <= u < v < k, "edge endpoints/order")
        require(not (g[u] >> v & 1), "repeated edge")
        g[u] |= 1 << v
        g[v] |= 1 << u
    return tuple(g)


def word(g):
    return "".join(str(g[i] >> j & 1)
                   for i in range(len(g)) for j in range(i + 1, len(g)))


def window(D):
    k, s = len(D), sum(D)
    return max(0, (s + 3*k - 83)//2), min(k*(k-1)//2, (s+k*(k-15))//2)


def valid(g, D):
    k = len(D)
    require(len(g) == k, "graph order")
    require(all(type(x) is int and 0 <= x < 1 << k for x in g),
            "invalid adjacency bitset")
    require(all(not (g[i] >> i & 1) for i in range(k)), "loop")
    require(all((g[i] >> j & 1) == (g[j] >> i & 1)
                for i in range(k) for j in range(i)), "asymmetry")
    h = tuple(x.bit_count() for x in g)
    require(all(h[i] <= min(4, k+D[i]-15) for i in range(k)), "filter i")
    lo, hi = window(D)
    require(2*lo <= sum(h) <= 2*hi, "filter ii")
    return h


def subset_pass(g, D):
    # Direct combinations and direct pair sums; no mask-sum recurrence.
    k, m = len(D), 21-len(D)
    c = [D[i]-1-g[i].bit_count() for i in range(k)]
    cap = {}
    for i, j in it.combinations(range(k), 2):
        upper = min(4, D[i]+D[j]-15) if g[i] >> j & 1 else 4
        cap[i, j] = upper-1-(g[i] & g[j]).bit_count()
    for size in range(1, k+1):
        for U in it.combinations(range(k), size):
            q, r = divmod(sum(c[i] for i in U), m)
            if m*q*(q-1)//2+r*q > sum(cap[p] for p in it.combinations(U, 2)):
                return False
    return True


def refine(g, D):
    # Equitable colour refinement is only a rejection invariant, never an
    # isomorphism verdict. Preserve its history to align labels across graphs.
    n = len(g)
    nb = [tuple(j for j in range(n) if g[i] >> j & 1) for i in range(n)]
    initial = [(D[i], len(nb[i])) for i in range(n)]
    palette = {s: j for j, s in enumerate(sorted(set(initial)))}
    colours = tuple(palette[s] for s in initial)
    history = [tuple(sorted(initial))]
    while True:
        sig = [(colours[i], tuple(sorted(colours[j] for j in nb[i])))
               for i in range(n)]
        history.append(tuple(sorted(sig)))
        palette = {s: j for j, s in enumerate(sorted(set(sig)))}
        new = tuple(palette[s] for s in sig)
        if len(set(new)) == len(set(colours)):
            return tuple(history), new
        colours = new


def maps(a, ca, b, cb, count=False):
    # Explicit bijection search, testing every adjacency and non-adjacency.
    n, full = len(a), (1 << len(a))-1
    domains = tuple(sum(1 << j for j in range(n) if cb[j] == ca[i])
                    for i in range(n))
    def search(left, ds):
        if not left:
            return 1
        u = min(left, key=lambda i: ds[i].bit_count())
        rest = tuple(i for i in left if i != u)
        choices, total = ds[u], 0
        while choices:
            bit = choices & -choices
            choices -= bit
            v = bit.bit_length()-1
            nxt = list(ds)
            for i in rest:
                allowed = b[v] if a[u] >> i & 1 else full ^ b[v]
                nxt[i] &= allowed & (full ^ bit)
                if not nxt[i]:
                    break
            else:
                total += search(rest, nxt)
                if total and not count:
                    return 1
        return total
    return search(tuple(range(n)), domains)


class Classes:
    def __init__(self, D):
        self.D, self.buckets, self.items = D, defaultdict(list), []

    def add(self, g):
        key, col = refine(g, self.D)
        for j in self.buckets[key]:
            h, hc = self.items[j]
            if maps(g, col, h, hc):
                return j, False
        j = len(self.items)
        self.items.append((g, col))
        self.buckets[key].append(j)
        return j, True

    def matches(self, g):
        key, col = refine(g, self.D)
        return [j for j in self.buckets.get(key, ())
                if maps(g, col, *self.items[j])]


def patterns(D):
    # Independently enumerate sorted within-cell degree vectors, including
    # nongraphical vectors (their labelled count is zero).
    k = len(D)
    lo, hi = window(D)
    blocks = [tuple(it.combinations_with_replacement(
        range(min(4, k+d-15)+1), D.count(d))) for d in (8, 9, 10)]
    for parts in it.product(*blocks):
        h = sum(parts, ())
        if sum(h) % 2 or not 2*lo <= sum(h) <= 2*hi:
            continue
        mult = math.prod(math.factorial(len(p)) //
                         math.prod(math.factorial(v) for v in Counter(p).values())
                         for p in parts)
        yield h, mult


def enumerate_labelled(h):
    # Adaptive maximum-demand vertex elimination, with NO symmetry pruning.
    # Every subset of its still-active labelled neighbours is considered.
    n, g = len(h), [0]*len(h)
    def visit(rem):
        active = tuple(i for i in range(n) if rem[i])
        if not active:
            yield tuple(g)
            return
        if any(rem[i] < 0 or rem[i] >= len(active) for i in active):
            return
        v = max(active, key=lambda i: (rem[i], -i))
        others = tuple(i for i in active if i != v)
        for chosen in it.combinations(others, rem[v]):
            rr = list(rem)
            rr[v] = 0
            for u in chosen:
                rr[u] -= 1
                g[v] |= 1 << u
                g[u] |= 1 << v
            yield from visit(tuple(rr))
            for u in chosen:
                g[v] ^= 1 << u
                g[u] ^= 1 << v
    yield from visit(tuple(h))


@lru_cache(None)
def F(ds):
    # Delete the LAST (largest-degree) vertex. Group neighbour choices by
    # residual degree; binomial coefficients count labelled subsets.
    if ds != tuple(sorted(ds)):
        return F(tuple(sorted(ds)))
    if not ds:
        return 1
    if ds[0] < 0 or ds[-1] >= len(ds) or sum(ds) % 2:
        return 0
    if ds[-1] == 0:
        return 1
    r, tail = ds[-1], ds[:-1]
    groups = tuple(sorted(Counter(tail).items()))
    def choose(j, need, residual, ways):
        if j == len(groups):
            return ways*F(tuple(sorted(residual))) if need == 0 else 0
        d, number = groups[j]
        total = 0
        for x in range(min(number, need)+1 if d else 1):
            total += choose(j+1, need-x,
                            residual+(d-1,)*x+(d,)*(number-x),
                            ways*math.comb(number, x))
        return total
    return choose(0, r, (), 1)


def read_case(path):
    d = json.loads(path.read_bytes())
    k, comp, hist = d["root"], tuple(d["composition"]), tuple(d["hist"])
    require(type(k) is int and k in (8, 9, 10), "root")
    require(len(comp) == len(hist) == 3 and
            all(type(x) is int and x >= 0 for x in comp+hist), "counts")
    require(sum(comp) == k and sum(hist) == 22 and hist[k-8] > 0, "counts/root")
    require(all(comp[i] <= hist[i]-(k == i+8) for i in range(3)), "composition")
    tag = "_".join(map(str, hist)) + f"_r{k}_c" + "".join(map(str, comp))
    require(path.name == "gen_"+tag+".json", "tag/JSON disagreement")
    raw = path.with_name("H_"+tag+".txt").read_bytes()
    lines = raw.decode("ascii").splitlines()
    require(len(lines) == d["count"] == len(d["cubes"]), "export length")
    D = tuple(d for d, n in zip((8, 9, 10), comp) for _ in range(n))
    graphs = []
    for line, rec in zip(lines, d["cubes"]):
        body, sep, comment = line.partition("#")
        edges = []
        for item in body.strip().split(",") if body.strip() else ():
            match = re.fullmatch(r"(\d+)-(\d+)", item.strip())
            require(match is not None, "text edge syntax")
            edges.append(tuple(int(x)-2 for x in match.groups()))
        g = graph(k, edges)
        jg = graph(k, [(u-2, v-2) for u, v in rec["edges"]])
        require(g == jg and word(g) == rec["word"], "JSON/text/word mismatch")
        require(sep and comment.strip() == f"t={rec['t']} aut={rec['aut']}",
                "text metadata")
        h = valid(g, D)
        require(rec["t"] == sum(h)//2, "edge count metadata")
        require(rec["columns"] == [D[i]-1-h[i] for i in range(k)], "columns")
        graphs.append(g)
    require(tuple(d["window"]) == window(D), "window metadata")
    return (k, comp), d, raw, graphs


def captured_census(path, d):
    spec = importlib.util.spec_from_file_location("untrusted_census", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    captured, predicate = [], mod.subset_ok
    def observe(g, degrees, m, tight88=False):
        # Observation at census's pre-subset boundary; no search changes.
        captured.append((tuple(g), sys._getframe(1).f_locals["aut"]))
        return predicate(g, degrees, m, tight88)
    mod.subset_ok = observe
    result = mod.census(d["hist"], d["root"], d["composition"], tight88=False)
    return captured, result


def check_family(key, cases, generator):
    start = time.perf_counter()
    k, comp = key
    ref, d, raw, exported = cases[0]
    D = tuple(v for v, n in zip((8, 9, 10), comp) for _ in range(n))
    method, errors = ("A" if k == 8 else "B"), []
    def check(ok, message):
        if not ok:
            errors.append(message)
    pre, survivors = Classes(D), Classes(D)
    total = sum(mult*F(h) for h, mult in patterns(D))
    group = math.prod(math.factorial(n) for n in comp)
    orbit = 0
    if method == "A":
        generated = 0
        for h, mult in patterns(D):
            number = 0
            for g in enumerate_labelled(h):
                number += 1
                require(tuple(x.bit_count() for x in g) == h, "A degrees")
                pre.add(g)
            check(number == F(h), f"A labelled count {h}: {number} != {F(h)}")
            generated += mult*number
        check(generated == total, "A weighted labelled count")
    else:
        captured, fresh = captured_census(generator, d)
        for i, (g, claimed_aut) in enumerate(captured):
            valid(g, D)
            j, new = pre.add(g)
            check(new, f"B isomorphic pre-representative {i} -> {j}")
            col = pre.items[j][1] if new else refine(g, D)[1]
            aut = maps(g, col, g, col, count=True)
            check(aut == claimed_aut, f"B aut {i}: {aut} != {claimed_aut}")
            require(aut > 0 and group % aut == 0, "invalid orbit divisor")
            orbit += group//aut
        check(orbit == total, f"B orbit {orbit} != recurrence {total}")
        check(fresh["before"] == len(captured), "B capture count")
    for g, col in pre.items:
        valid(g, D)
        if method == "A":
            aut = maps(g, col, g, col, count=True)
            require(aut > 0 and group % aut == 0, "invalid A orbit divisor")
            orbit += group//aut
        if subset_pass(g, D):
            survivors.add(g)
    check(orbit == total, f"independent orbit {orbit} != recurrence {total}")
    matched, hits = 0, Counter()
    for i, g in enumerate(exported):
        matches = survivors.matches(g)
        check(len(matches) == 1, f"export {i}: survivor matches {matches}")
        if len(matches) == 1:
            matched += 1
            hits[matches[0]] += 1
        col = refine(g, D)[1]
        aut = maps(g, col, g, col, count=True)
        for path, data, _, _ in cases:
            check(data["cubes"][i]["aut"] == aut, f"{path.name}: aut {i}")
    check(all(hits[j] == 1 for j in range(len(survivors.items))),
          "survivor/export bijection fails (missing or duplicate class)")
    if method == "B":
        actual = {word(g) for g, _ in survivors.items}
        check([word(g) for g in exported] == sorted(actual),
              "B labelled survivor/export disagreement")
        check({r["word"] for r in fresh["cubes"]} == actual and
              len(fresh["cubes"]) == len(actual), "B generator filter disagreement")
    for path, data, data_raw, _ in cases:
        check(data_raw == raw, f"{path.name}: list bytes differ from {ref.name}")
        check(data["before"] == len(pre.items), f"{path.name}: before")
        check(data["count"] == len(survivors.items), f"{path.name}: count")
        check(data["F"] == data["orbit"] == total, f"{path.name}: F/orbit")
    print(k, ",".join(map(str, comp)), method, len(pre.items),
          len(survivors.items), len(exported), matched, len(errors),
          f"{time.perf_counter()-start:.3f}", flush=True)
    for error in errors:
        print("MISMATCH", key, error, flush=True)
    return len(errors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lists", type=Path, default=Path("runs/k28_rooted"))
    parser.add_argument("--generator", type=Path,
                        default=Path("scripts/astra/census_gen.py"))
    parser.add_argument("--family", action="append", help="k,n8,n9,n10; repeatable")
    args = parser.parse_args()
    families, digest, tags = defaultdict(list), hashlib.sha256(), 0
    paths = sorted(args.lists.glob("gen_*.json"))
    for path in paths:
        if path.name == "gen_manifest.json":
            continue
        key, d, raw, exported = read_case(path)
        families[key].append((path, d, raw, exported))
        for name, blob in ((path.name, path.read_bytes()),
                           (path.name.replace("gen_", "H_").replace(".json", ".txt"), raw)):
            for chunk in (name.encode(), blob):
                digest.update(len(chunk).to_bytes(8, "big"))
                digest.update(chunk)
        tags += 1
    require(tags > 0, "no cases")
    requested = None
    if args.family:
        requested = set()
        for item in args.family:
            k, a, b, c = map(int, item.split(","))
            requested.add((k, (a, b, c)))
        require(requested <= families.keys(), "unknown requested family")
    order = sorted(families, key=lambda x:
                   ({8: 0, 10: 1, 9: 2}[x[0]],
                    tuple(-v for v in x[1]) if x[0] == 10 else x[1]))
    print("INPUT", tags, "tags", len(families), "families SHA256", digest.hexdigest(),
          flush=True)
    print("k composition method pre-filter survivors listed matched mismatches seconds",
          flush=True)
    errors, completed = 0, 0
    for key in order:
        if requested is not None and key not in requested:
            continue
        errors += check_family(key, families[key], args.generator)
        completed += 1
    print("COMPLETE" if completed == len(families) else "PARTIAL",
          completed, "/", len(families), "families; mismatches", errors, flush=True)
    return 1 if errors else (0 if completed == len(families) else 2)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print("ERROR", type(exc).__name__, str(exc), file=sys.stderr, flush=True)
        sys.exit(1)
