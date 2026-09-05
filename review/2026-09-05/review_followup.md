# External review, second message (2026-09-05)

Same reviewer and same commit under review (784339a) as `review.md`. The text below is reproduced verbatim. The one edit is the link target for the checker, which pointed at a path on the author's machine and now points at the copy deposited in this directory as `check_witnesses.py`. The JSON files in this directory (`witness-results.json`, `independent-cover-results.json`, `proof-sample-results.json`, `coverage-negative-control.json`) are the reviewer's own outputs referred to below.

---

I used two different levels of verification. **I fully checked the constructions that close three cells using published upper bounds. I did not fully verify the three closures requiring new exhaustive refutations.**

For the first three, I wrote a [separate Python checker](check_witnesses.py) that imports no repository code. It checks that every edge appears exactly once, then enumerates **every vertex pair in each color** and counts their common neighbors.

This works because a graph contains \(K_{2,t}\) exactly when some pair has at least \(t\) common neighbors. The pair itself need not be an edge.

| Claimed closure | Deposited coloring | Maximum common neighbors, colors 1 / 2 | Forbidden thresholds |
|---|---:|---:|---:|
| \(R(K_{2,10},K_{2,7})=31\) | \(K_{30}\) | 9 / 6 | 10 / 7 |
| \(R(K_{2,10},K_{2,6})=29\) | \(K_{28}\) | 9 / 5 | 10 / 6 |
| \(R(K_{2,2},K_{2,19})=29\) | \(K_{28}\) | 1 / 18 | 2 / 19 |

Thus the colorings prove lower bounds of **31, 29, and 29**. Those match the upper bounds I checked in [DS1.18, Table IVc and §3.3.1(f)](https://www.cs.rit.edu/~spr/ElJC/sur.pdf). **I relied on those published upper bounds; I did not independently reprove them.**

For the other three proposed closures—\(K_{3,4}/K_{3,3}=19\), \(K_{3,5}/K_{2,4}=19\), and \(K_{3,5}/K_{2,5}=22\)—I checked:

- Their lower-bound colorings against the graph definitions.
- Reconstructed formulas against deposited clause bodies and certificate-ledger hashes.
- Ledger completeness and, for n=22, agreement between the retained tree and flat leaf list.
- **Actual proof certificates for all three cube covers.** These establish that the search partitions omit no assignments.
- The one deposited sample leaf refutation, which passed `lrat-check`.

**What remains unchecked is decisive:** I did not replay every leaf’s UNSAT proof or verify the private formal encoding-soundness development. Ledger entries saying “verified” are evidence of reported checks, not independent proof replay.

So my earlier wording “three exact values check out” means **independently verified lower-bound witnesses plus accepted published upper bounds**. The remaining three exact values were not certified by my review.
