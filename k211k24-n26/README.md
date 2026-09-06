# K(2,11) / K(2,4) at n = 26

Forbidden: **K_{2,11} in color 1, K_{2,4} in color 2**. DS1 rev #18 Table IVc (row n = 11, column
m = 4) prints `>= 25`; the survey's general bound 3.3.2(j), R(K_{2,n-s}, K_{2,n}) <= 4n - 2s - 3,
gives <= 27 (n = 11, s = 7). Our coloring of K_25 in `../k2x11-k2x4-lb26/` raised the lower bound to
26, so the cell was open at 26-27, one wide: a refutation at n = 26 closes it and a coloring of
K_26 would have closed it at 27.

**Both bounds are ours.** The lower bound is the K_25 coloring in `../k2x11-k2x4-lb26/` (checkable
by subgraph containment alone). `instance/` holds the formula for n = 26 in the deposited encoding
(`tools/gen_ramsey.py 26 K2x11,K2x4 --vertex-lex`), `tree/` the cube tree of its refutation: 402 top
cubes (march_cu, depth 10), 49 cubes resplit at depth 8 (cap 120 s) over three levels, 10,017 leaves,
every leaf UNSAT with its LRAT proof checked at solve time (lrat-trim, lrat-check), 0 SAT, 48,416
core-seconds on 16 vCPU (2026-09-06). `tree/cover_audit_2026-09-06.txt` is the audit: every leaf has a
checked verdict and the negation of all 10,017 leaves is refuted with a checked LRAT proof, so the
cubes cover every assignment. Together **R(K_{2,11}, K_{2,4}) = 26**.

`certificate/` holds the Comparator statement for this formula (`Encoder.k211k24_n26`, the Lean encoder
whose printed CNF, sha256 72b4e9cc..., equals `instance/k211k24_n26.cnf` clause for clause and in order;
the deposited file only adds six comment lines), its two external verdict axioms discharged by cake_lpr
(leaves and cover), the cake_lpr ledger (`k211k24_cakelpr_encoder_ledger.jsonl`, 10,017 leaves + cover,
all VERIFIED), the leaf hashes recomputed on a second machine (`k211k24_encoder_leaf_sha256.txt`,
10,017/10,017 match), and the PASS transcript (`PASS_lrat-catcher-k211k24_2026-09-06.log`, Lean kernel
and nanoda both accept; see `certificate/CERTIFICATE_k211k24.md`).

The refutation needs the encoding to be faithful, the symmetry breaking to be sound, and the cube cover
to be exhaustive. The cover is machine-checked (above). The encoding and the vertex-lex symmetry
breaking are argued in the private Lean development described in `../REVIEWER.md` section 5; the
public chain ends at "this CNF is unsatisfiable".

Method note: the deposited encoding was chosen for this cell by the sampled cube protocol described
in `../FINDINGS.md` (2026-09-06): sixty sampled cubes solved 60/60 under it (mean 5.3 s, about 2,150
core-seconds projected) against about 27,700 core-seconds projected under the degree-ordering
formula; the closed tree cost 48,416 core-seconds, the projection having missed the capped cubes.

## Check: cover and tree structure (leaf verdicts read from the ledger)

```
python3 ../tools/verify_close.py instance/k211k24_n26.cnf instance/k211k24_n26_d10.icnf tree --check-all
```
This re-proves and checks the cover (negation of all leaves) and walks the tree for gaps; the leaf
verdicts themselves are read from the ledger because the solve-time proof files were deleted, and
the tool now says so in its SCOPE line. It is not a complete independent replay.

## Full replay: re-solve every leaf

`../tools/cert_pass.py` rebuilds every leaf from the Lean-printed base and prefixes in `certificate/`
and checks each fresh proof with cake_lpr (that is how the deposited ledger was made);
`../tools/proof_archive.py` does the same and keeps every trimmed proof (lrat-trim, checked again with
lrat-check and cake_lpr, xz-compressed) with a manifest of hashes. The archived proofs for this cell
(about 30 GB compressed) are being built and will be attached to a release of this repository in 2 GB
parts; `certificate/CERTIFICATE_k211k24.md` names the release once it exists.
