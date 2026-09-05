"""Independent audit of deposited complete two-colour graphs; standard library only."""
import itertools, json, pathlib, re, sys

root = pathlib.Path(sys.argv[1])
results = []
for path in sorted(root.glob('*/witness/witness_*.txt')):
    raw = path.read_text()
    spec = re.search(r'^# spec: (.+)$', raw, re.M).group(1).strip().split(',')
    assert len(spec) == 2
    edges = {}
    for line in raw.splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        u, v, c = map(int, line.split())
        assert 1 <= u < v and c in (1, 2), (path, line)
        assert (u, v) not in edges, (path, 'duplicate', u, v)
        edges[u, v] = c
    n = max(max(e) for e in edges)
    vertices = set(range(1, n + 1))
    assert set(edges) == set(itertools.combinations(range(1, n + 1), 2)), (path, 'incomplete')
    checks = []
    for color, token in enumerate(spec, 1):
        nbr = {u: {v for v in vertices - {u} if edges[tuple(sorted((u, v)))] == color} for u in vertices}
        bip = re.fullmatch(r'K(\d+)x(\d+)', token)
        book = re.fullmatch(r'B(\d+)', token)
        if bip:
            s, threshold = map(int, bip.groups())
            candidates = list(itertools.combinations(sorted(vertices), s))
        elif book:
            threshold = int(book.group(1))
            candidates = [e for e in edges if edges[e] == color]
        else:
            raise ValueError(token)
        counts = [(len(set.intersection(*(nbr[u] for u in S))), S) for S in candidates]
        maximum, where = max(counts)
        assert maximum < threshold, (path, color, token, maximum, where)
        checks.append({'color': color, 'forbidden': token, 'sets_checked': len(counts), 'maximum_common_neighbors': maximum, 'required_for_violation': threshold})
    results.append({'path': str(path.relative_to(root)), 'n': n, 'edges': len(edges), 'valid': True, 'checks': checks})
print(json.dumps(results, indent=2))
