#!/usr/bin/env python3
"""Exhaustive semantic check of the census encoder (rooted_encode.rooted_formula).

WHY THIS EXISTS. Everything the campaign claims rests on UNSAT results from this encoder. If it
OVER-constrains -- rejects colourings the mathematics permits -- then UNSAT does not mean "no good
colouring exists" and all 23,886 refutations are worthless. Every certificate would still verify
and still prove nothing. That is the failure this test is built to catch.

WHAT CORRECTNESS MEANS HERE, which is subtler than it first looks. The encoder is NOT
model-equivalent to the mathematical condition, and must not be expected to be: it breaks symmetry
WITHIN degree cells. Vertices in the same cell are interchangeable, so the formula admits only
canonical representatives. Writing the naive model-equivalence test first shows this immediately --
at N=6 the mathematics admits 5 colourings and the encoder accepts 3, and the 2 it rejects are
exactly the within-cell permutations of 2 it accepts.

The property that actually matters, and that this checks:

  SOUNDNESS   no colouring the mathematics forbids is accepted
  COMPLETENESS  no ORBIT is lost: every equivalence class of admissible colourings, under
                permutations that fix the cell structure, has at least one accepted member

Completeness in that form is what makes UNSAT meaningful: if a good colouring existed, some
canonical representative of it would satisfy the formula, so UNSAT rules out the whole orbit.

Usage: python3 scripts/referee/encoder_equiv_test.py
"""
import itertools, os, subprocess, sys, tempfile, random

HERE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(HERE, 'ramsey', 'scripts', 'lemma'))
sys.path.insert(0, os.path.join(HERE, 'ramsey'))
sys.path.insert(0, os.path.join(os.path.abspath('.'), 'scripts', 'lemma'))
sys.path.insert(0, os.path.abspath('.'))
from rooted_encode import rooted_formula, edge_index, cells_of

CAD = os.environ.get('CADICAL', 'cadical')


def sat_with(cls, nv, units):
    fd, p = tempfile.mkstemp(suffix='.cnf'); os.close(fd)
    try:
        with open(p, 'w') as f:
            f.write(f'p cnf {nv} {len(cls) + len(units)}\n')
            for c in cls:
                f.write(' '.join(map(str, c)) + ' 0\n')
            for u in units:
                f.write(f'{u} 0\n')
        return subprocess.run([CAD, '-q', p], capture_output=True, text=True).returncode == 10
    finally:
        os.unlink(p)


def admissible(N, s, t, D, k, H, blue):
    """The mathematical condition, written from the definitions and NOT from the encoder."""
    V = range(1, N + 1)
    ib = lambda u, v: frozenset((u, v)) in blue
    for v in V:                                   # prescribed blue degree
        if sum(1 for u in V if u != v and ib(u, v)) != D[v - 1]:
            return False
    for u in V:                                   # root's blue neighbourhood is exactly 2..k+1
        if u != 1 and ib(1, u) != (2 <= u <= k + 1):
            return False
    for x, y in itertools.combinations(V, 2):     # codegree caps
        if sum(1 for w in V if w not in (x, y) and not ib(w, x) and not ib(w, y)) > s - 1:
            return False
        if sum(1 for w in V if w not in (x, y) and ib(w, x) and ib(w, y)) > t - 1:
            return False
    for x, y in itertools.combinations(range(2, k + 2), 2):   # cube: H fixes N(root) internally
        if ib(x, y) != (frozenset((x, y)) in H):
            return False
    return True


def cell_perms(ncells, wcells):
    """Permutations of vertices that preserve the cell structure: any rearrangement within a cell.
    The root is fixed. These are exactly the symmetries the encoder is entitled to break."""
    blocks = [list(range(lo, hi + 1)) for lo, hi, _d in list(ncells) + list(wcells)]
    per_block = [list(itertools.permutations(b)) for b in blocks]
    out = []
    for combo in itertools.product(*per_block):
        m = {1: 1}
        for b, img in zip(blocks, combo):
            for src, dst in zip(b, img):
                m[src] = dst
        out.append(m)
    return out


def run(N, colors, degs, k, comp, H, sample_neg=600, seed=7, mutate=None, **enc):
    s = int(colors[0].split('x')[1]); t = int(colors[1].split('x')[1])
    D, ncells, wcells = cells_of(N, degs, k, comp)
    cls, nv, _c, _h, _D = rooted_formula(N, colors, degs, k, comp,
                                         H=sorted(tuple(sorted(e)) for e in H),
                                         base_codegree=False, **enc)
    if mutate == 'overconstrain':
        # Inject a spurious clause forbidding edge 0 from being blue. This removes real solutions
        # without making the formula unsatisfiable outright -- exactly the failure mode that would
        # make every UNSAT in the census meaningless while leaving all certificates valid. If the
        # test cannot see THIS, it cannot see anything.
        cls = cls + [[-(edge_index(N)[sorted(edge_index(N), key=lambda e: edge_index(N)[e])[0]] * len(colors) + 2)]]
    elif mutate == 'underconstrain':
        # Keep ONLY the "exactly one colour per edge" clauses, dropping the counting machinery that
        # enforces degrees and codegree caps. A first attempt dropped just one edge's clauses and
        # the test passed -- not because the test was sound but because a 600-sample rarely meets
        # the few colourings that one edge affects. A control has to be decisive enough that a
        # blind test cannot survive it by luck.
        pass          # applied below, once the edge list is known
    eidx = edge_index(N); nc = len(colors)
    edges = sorted(eidx, key=lambda e: eidx[e])
    if mutate == 'underconstrain':
        cls = [c for c in cls if all(abs(l) <= len(edges) * nc for l in c)]
    Hs = {frozenset(e) for e in H}
    units = lambda m: [eidx[e] * nc + (2 if (m >> i & 1) else 1) for i, e in enumerate(edges)]

    print(f'  N={N} {colors} degs={degs} root={k} comp={comp} |H|={len(H)}  '
          f'({nv} vars, {len(cls)} clauses, 2^{len(edges)} colourings)')

    adm = []
    for m in range(1 << len(edges)):
        blue = {frozenset(e) for i, e in enumerate(edges) if m >> i & 1}
        if admissible(N, s, t, D, k, Hs, blue):
            adm.append((m, blue))
    print(f'    mathematics admits {len(adm)}')

    perms = cell_perms(ncells, wcells)
    admset = {m for m, _ in adm}
    def canon(blue):
        best = None
        for p in perms:
            img = frozenset(frozenset((p[u], p[v])) for u, v in (tuple(e) for e in blue))
            key = tuple(sorted(tuple(sorted(e)) for e in img))
            if best is None or key < best: best = key
        return best
    orbits = {}
    for m, blue in adm:
        orbits.setdefault(canon(blue), []).append(m)
    print(f'    orbits under cell-preserving permutations: {len(orbits)}  '
          f'(group order {len(perms)})')

    accepted = {m for m, _ in adm if sat_with(cls, nv, units(m))}
    lost = [o for o, ms in orbits.items() if not (set(ms) & accepted)]
    if not adm:
        # A case the mathematics admits nothing in passes COMPLETENESS vacuously and tests nothing
        # on the side that matters. Say so rather than letting it read as a pass.
        print('    COMPLETENESS: VACUOUS -- mathematics admits no colouring here, so this case '
              'exercises only SOUNDNESS')
    else:
        print(f'    COMPLETENESS: orbits with no accepted representative: {len(lost)} '
              f'of {len(orbits)}  <- must be 0')

    random.seed(seed)
    others = [m for m in range(1 << len(edges)) if m not in admset]
    samp = random.sample(others, min(sample_neg, len(others)))
    wrong = [m for m in samp if sat_with(cls, nv, units(m))]
    print(f'    SOUNDNESS: forbidden colourings accepted: {len(wrong)} of {len(samp)} '
          f'sampled  <- must be 0')
    return not lost and not wrong


if __name__ == '__main__':
    # Exhaustive enumeration is 2^(N(N-1)/2), so N=7 (2^21) is the practical ceiling. Coverage is
    # widened by varying the STRUCTURE the encoder has to get right -- number of degree cells, root
    # degree, how the cube constrains N(root), and the codegree caps -- rather than by growing N.
    cases = [
        # two cells, empty cube, symmetric caps
        dict(N=6, colors=['K2x3', 'K2x3'], degs=[2, 2, 2, 2, 3, 3], k=2, comp={2: 1, 3: 1}, H=[]),
        # asymmetric caps: red cap looser than blue
        dict(N=6, colors=['K2x4', 'K2x3'], degs=[2, 2, 2, 2, 3, 3], k=2, comp={2: 1, 3: 1}, H=[]),
        # larger root, non-empty cube: exercises the H units inside N(root)
        dict(N=7, colors=['K2x4', 'K2x3'], degs=[2, 2, 2, 3, 3, 3, 3], k=3, comp={2: 1, 3: 2},
             H=[(2, 3)]),
        # same case with a DIFFERENT cube: the cube must actually change what is admitted
        dict(N=7, colors=['K2x4', 'K2x3'], degs=[2, 2, 2, 3, 3, 3, 3], k=3, comp={2: 1, 3: 2},
             H=[(2, 4)]),
        # a full cube on N(root): admits nothing, so it exercises SOUNDNESS only. Kept because an
        # encoder that accepted something here would be badly wrong, and the report says VACUOUS
        # rather than pretending the completeness half was tested.
        dict(N=7, colors=['K2x4', 'K2x3'], degs=[2, 2, 2, 3, 3, 3, 3], k=3, comp={2: 1, 3: 2},
             H=[(2, 3), (2, 4), (3, 4)]),
        # a two-edge cube that still leaves solutions, so completeness IS exercised under a cube
        dict(N=7, colors=['K2x5', 'K2x4'], degs=[2, 3, 3, 3, 3, 4, 4], k=3, comp={3: 2, 4: 1},
             H=[(2, 3)]),
        # root drawn from the LOWER degree class, composition weighted the other way
        dict(N=7, colors=['K2x4', 'K2x4'], degs=[2, 3, 3, 3, 3, 3, 3], k=2, comp={3: 2}, H=[]),
        # three distinct degree values -> three cells, so the wall has more than one block
        dict(N=7, colors=['K2x4', 'K2x4'], degs=[2, 2, 3, 3, 3, 4, 5], k=3, comp={2: 1, 3: 2},
             H=[]),
        # the real cell's caps (r=7, b=4). Vacuous at this size, which is the point: the encoder
        # must not invent constraints when the caps cannot bite.
        dict(N=6, colors=['K2x8', 'K2x5'], degs=[2, 2, 2, 2, 3, 3], k=2, comp={2: 1, 3: 1}, H=[]),
    ]
    allok = True
    for i, c in enumerate(cases, 1):
        print(f'--- case {i}')
        allok &= run(**c)

    # Negative controls: the test must FAIL on a deliberately broken encoder, or it proves nothing.
    print('\n--- negative controls (these MUST fail)')
    ctrl = dict(cases[0])
    over = run(**ctrl, mutate='overconstrain')
    print(f'    over-constrained encoder -> {"PASS (BAD: test is blind)" if over else "correctly FAILED"}')
    under = run(**ctrl, mutate='underconstrain')
    print(f'    under-constrained encoder -> {"PASS (BAD: test is blind)" if under else "correctly FAILED"}')

    good = allok and not over and not under
    print('\nRESULT:', 'PASS' if good else 'FAIL')
    sys.exit(0 if good else 1)
