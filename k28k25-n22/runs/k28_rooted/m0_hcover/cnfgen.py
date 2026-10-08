"""M0 H-only cover CNF builder (shared by build and validate; Python >= 3.9, stdlib only).

Family = (k, comp) with comp = (#N8, #N9, #N10). Vertices 0..k-1 of N in cell order (degree 8 cell first),
exactly as census_gen.census builds `degrees`. Graph variables: x_e for e = (i,j), i<j, in row-major order
(itertools.combinations order) = the order of census_gen.canon's word; var(e) = index+1.

Clause groups (all CNF; aux variables are defined one-directionally, which is sound for refutation):
  (i)   H-degree caps  h_i <= min(4, k + D_i - 15)       : direct clauses, one per (cap+1)-subset of the row
  (ii)  edge window    lo <= t <= hi (LEMMAS 4.2)        : Sinz sequential counters (at-most hi on x, at-most E-lo on -x)
  (LL)  lex-leader     x <=lex x o p  for each p in P    : p a cell-preserving vertex permutation; (x o p)_{ij} = x_{p(i)p(j)}
  (B)   blockers       one clause per blocked word w     : excludes exactly the labelled graph with word w
"""
from itertools import combinations


def family_params(k, comp):
    degrees = tuple(sum(((d,) * comp[d - 8] for d in (8, 9, 10)), ()))
    assert len(degrees) == k
    S = sum(degrees)
    lo = max(0, -(-(S + 3 * k - 84) // 2))
    hi = min(k * (k - 1) // 2, (S + k * (k - 15)) // 2)
    caps = tuple(min(4, k + d - 15) for d in degrees)
    return degrees, caps, lo, hi


def pairs(k):
    return tuple(combinations(range(k), 2))


def cells(degrees):
    return [tuple(i for i, d in enumerate(degrees) if d == c) for c in sorted(set(degrees))]


def is_cell_perm(p, degrees):
    k = len(degrees)
    return sorted(p) == list(range(k)) and all(degrees[p[i]] == degrees[i] for i in range(k))


class Builder:
    def __init__(self, k, comp):
        self.k, self.comp = k, tuple(comp)
        self.degrees, self.caps, self.lo, self.hi = family_params(k, comp)
        self.P = pairs(k)
        self.E = len(self.P)
        self.var = {e: n + 1 for n, e in enumerate(self.P)}
        self.nv = self.E
        self.base = []
        self._degree_caps()
        self._window()

    def new(self):
        self.nv += 1
        return self.nv

    def x(self, i, j):
        return self.var[(i, j) if i < j else (j, i)]

    def _degree_caps(self):
        k = self.k
        for i in range(k):
            row = [self.x(i, j) for j in range(k) if j != i]
            c = self.caps[i]
            if c < 0:
                self.base.append([])
                continue
            for sub in combinations(row, c + 1):
                self.base.append([-v for v in sub])

    def _atmost(self, lits, K):
        """Sinz sequential counter: sum(lits) <= K. s[i][j] -> 'at least j+1 of lits[0..i] true'."""
        n = len(lits)
        if K >= n:
            return
        if K < 0:
            self.base.append([])
            return
        if K == 0:
            for l in lits:
                self.base.append([-l])
            return
        s = [[self.new() for _ in range(K)] for _ in range(n - 1)]
        cl = self.base
        cl.append([-lits[0], s[0][0]])
        for j in range(1, K):
            cl.append([-s[0][j]])
        for i in range(1, n - 1):
            cl.append([-lits[i], s[i][0]])
            cl.append([-s[i - 1][0], s[i][0]])
            for j in range(1, K):
                cl.append([-lits[i], -s[i - 1][j - 1], s[i][j]])
                cl.append([-s[i - 1][j], s[i][j]])
            cl.append([-lits[i], -s[i - 1][K - 1]])
        cl.append([-lits[n - 1], -s[n - 2][K - 1]])

    def _window(self):
        xs = list(range(1, self.E + 1))
        self._atmost(xs, self.hi)
        self._atmost([-v for v in xs], self.E - self.lo)

    def ll_clauses(self, p):
        """x <=lex y with y_e = x_{p(e)}. Returns clause list; allocates aux vars."""
        out = []
        a = None  # None == literal 'true' (prefix equal so far, unconditionally)
        seq = []
        for e in self.P:
            i, j = e
            f = (p[i], p[j]) if p[i] < p[j] else (p[j], p[i])
            if f == e:
                continue
            seq.append((self.var[e], self.var[f]))
        for n, (xv, yv) in enumerate(seq):
            last = n == len(seq) - 1
            g = [] if a is None else [-a]
            out.append(g + [-xv, yv])           # a -> x <= y
            if last:
                break
            a2 = self.new()
            out.append(g + [-xv, a2])           # a & x  -> (y=1, equal) -> a2
            out.append(g + [yv, a2])            # a & -y -> (x=0, equal) -> a2
            a = a2
        return out

    def blocker(self, word):
        assert len(word) == self.E
        return [(-(n + 1) if c == '1' else (n + 1)) for n, c in enumerate(word)]

    def dimacs(self, ll_list, blocked_words, comments=()):
        """ll_list: list of clause-lists (already allocated, in order). Returns DIMACS text."""
        cls = list(self.base)
        for c in ll_list:
            cls.extend(c)
        for w in blocked_words:
            cls.append(self.blocker(w))
        head = "".join(f"c {t}\n" for t in comments)
        body = "".join(" ".join(map(str, c)) + " 0\n" for c in cls)
        return head + f"p cnf {self.nv} {len(cls)}\n" + body


def build_full(k, comp, perms, blocked_words, comments=()):
    """Deterministic: base, then LL(p) for p in perms (aux allocated in that order), then blockers."""
    b = Builder(k, comp)
    ll = [b.ll_clauses(p) for p in perms]
    return b, b.dimacs(ll, blocked_words, comments)


def word_of(g, k):
    return "".join(str(g[i] >> j & 1) for i in range(k) for j in range(i + 1, k))


def graph_of(word, k):
    g = [0] * k
    for n, (i, j) in enumerate(pairs(k)):
        if word[n] == '1':
            g[i] |= 1 << j
            g[j] |= 1 << i
    return tuple(g)
