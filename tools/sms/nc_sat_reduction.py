#!/usr/bin/env python3
"""Independent adjudicator: reduce each (clause, witness) to a SAT instance and let an
EXTERNAL CDCL solver (cadical) decide it.  UNSAT == witness valid over ALL completions.

Encoding.  Edge vars e_0..e_{m-1} (row-major upper triangle).  Prefix-equality vars p_0..p_m.
F = negation of the clause (unit clauses).  p_0 = true.
For each position k with y = e_k and x = e_{sigma(k)}:
   (~p_k | x | ~y)                        # forbid "first difference has piG smaller"
   (~p_k | x | y | p_{k+1})               # p_{k+1} <- p_k & (x=y=0)
   (~p_k | ~x | ~y | p_{k+1})             # p_{k+1} <- p_k & (x=y=1)
SAT  => a completion with vec(pi.G) >= vec(G) exists => witness FAILS.
UNSAT=> every completion has vec(pi.G) < vec(G)      => witness OK.
"""
import json, subprocess, sys, os, tempfile

CAD = os.environ.get("CADICAL", os.path.expanduser("~/sat/cadical/build/cadical"))

def pairs_of(n):
    return [(u, v) for u in range(n) for v in range(u + 1, n)]

def build(clause, perm, n, pairs, idx, inverse=False):
    m = len(pairs)
    p = list(perm)
    if inverse:
        inv = [0]*n
        for i, x in enumerate(p): inv[x] = i
        p = inv
    E = lambda k: k + 1              # edge var k -> 1..m
    P = lambda k: m + 1 + k          # prefix var k -> m+1..m+1+m
    cls = []
    for s, u, v in clause:
        k = idx[(u, v) if u < v else (v, u)]
        cls.append([-E(k)] if s == 1 else [E(k)])   # falsify the literal
    cls.append([P(0)])
    for k, (u, v) in enumerate(pairs):
        a, b = p[u], p[v]
        q = idx[(a, b) if a < b else (b, a)]
        x, y = E(q), E(k)
        cls.append([-P(k), x, -y])
        cls.append([-P(k), x, y, P(k+1)])
        cls.append([-P(k), -x, -y, P(k+1)])
    return m + 1 + m, cls

def solve(nv, cls, tmp):
    with open(tmp, "w") as f:
        f.write("p cnf %d %d\n" % (nv, len(cls)))
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    r = subprocess.run([CAD, "-q", tmp], capture_output=True, text=True)
    if r.returncode == 20: return "UNSAT"
    if r.returncode == 10: return "SAT"
    raise RuntimeError("solver rc=%d %s" % (r.returncode, r.stdout[:200]))

def main():
    path, n = sys.argv[1], int(sys.argv[2])
    inverse = "--inverse" in sys.argv
    data = json.load(open(path))
    entries = data["sym_clauses"]
    pairs = pairs_of(n); idx = {pq: i for i, pq in enumerate(pairs)}
    tmp = tempfile.mktemp(suffix=".cnf")
    ok = fail = 0
    for i, (clause, perm) in enumerate(entries):
        assert sorted(perm) == list(range(n)), "bad perm at %d" % i
        nv, cls = build(clause, perm, n, pairs, idx, inverse)
        r = solve(nv, cls, tmp)
        if r == "UNSAT":
            ok += 1; print("%d OK" % i)
        else:
            fail += 1; print("%d FAIL sat-counterexample-exists" % i)
    print("TOTAL %d OK %d FAIL %d" % (len(entries), ok, fail))

if __name__ == '__main__':
    main()