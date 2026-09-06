# K(2,11) / K(2,3) at n = 22

Forbidden: **K_{2,11} in color 1, K_{2,3} in color 2**. DS1 rev #18 Table IVc (row n = 11, column
m = 3) prints `>= 22` with source [VO]; the survey's general bound 3.3.2(j),
R(K_{2,n-s}, K_{2,n}) <= 4n - 2s - 3, gives <= 25 (n = 11, s = 8). So the cell was open at 22-25.

**The lower bound is not ours.** R >= 22 is Van Overberghe's (a coloring of K_21; survey tag [VO],
now in [GoeVO]). No coloring is deposited here. `instance/` holds the formula for n = 22 in the
deposited encoding (`tools/gen_ramsey.py 22 K2x11,K2x3 --vertex-lex`), `tree/` the cube tree of its
refutation: 374 top cubes (march_cu, depth 10), 4 cubes resplit at depth 8 (cap 120 s), 1,313 leaves,
every leaf UNSAT with its LRAT proof checked at solve time (lrat-trim, lrat-check), 0 SAT, 5,628
core-seconds on 16 vCPU (2026-09-06). `tree/cover_audit_2026-09-06.txt` is the audit: every leaf has a
checked verdict and the negation of all 1,313 leaves is refuted with a checked LRAT proof, so the cubes
cover every assignment. Together **R(K_{2,11}, K_{2,3}) = 22**.

`certificate/` holds the Comparator statement for this formula (`Encoder.k211k23_n22`, the Lean encoder
whose printed CNF, sha256 57518b8c..., equals `instance/k211k23_n22.cnf` clause for clause and in order;
the deposited file only adds six comment lines), its two external verdict axioms discharged by cake_lpr
(leaves and cover), the cake_lpr ledger (`k211k23_cakelpr_encoder_ledger.jsonl`, 1,313 leaves + cover,
all VERIFIED), the leaf hashes recomputed on a second machine (`k211k23_encoder_leaf_sha256.txt`,
1,313/1,313 match), and the PASS transcript (`PASS_lrat-catcher-k211k23_2026-09-06.log`, Lean kernel
and nanoda both accept; see `certificate/CERTIFICATE_k211k23.md`).

The refutation needs the encoding to be faithful, the symmetry breaking to be sound, and the cube cover
to be exhaustive. The cover is machine-checked (above). The encoding and the vertex-lex symmetry
breaking are argued in the private Lean development described in `../REVIEWER.md` section 5; the
public chain ends at "this CNF is unsatisfiable".

Method note: the same cell under the degree-ordering formula of `k28k25-n22/` measured about twenty
times more expensive in a sampled cube protocol (see `../FINDINGS.md`, 2026-09-06); the deposited
encoding was used for that reason.

## Check: cover and tree structure (leaf verdicts read from the ledger)

```
python3 ../tools/verify_close.py instance/k211k23_n22.cnf instance/k211k23_n22_d10.icnf tree --check-all
```
This re-proves and checks the cover (negation of all leaves) and walks the tree for gaps; the leaf
verdicts themselves are read from the ledger because the solve-time proof files were deleted, and
the tool now says so in its SCOPE line. It is not a complete independent replay.

## Full replay: re-solve every leaf

`../tools/cert_pass.py` rebuilds every leaf from the Lean-printed base and prefixes in `certificate/`
and checks each fresh proof with cake_lpr (that is how the deposited ledger was made);
`../tools/proof_archive.py` does the same and keeps every trimmed proof (lrat-trim, checked again with
lrat-check and cake_lpr, xz-compressed) with a manifest of hashes. The archived proofs of this cell are
attached to the release `proofs-k211k23-n22-2026-09-06` of this repository: `proofs_part00.tar`
(1,313 files `leaf_<i>.lrat.xz`, 1.40 GB, sha256 81b8aa04...), `manifest.jsonl` (per leaf: leaf-CNF
sha256, trimmed-proof sha256, .xz sha256, verdicts; a copy is `certificate/proof_archive_manifest.jsonl`),
the printed inputs `base_encoder.cnf.xz`, `prefixes.tsv.xz`, `negcubes.cnf.xz`, and `SHA256SUMS.txt`.
Every archived proof was accepted by lrat-check and by cake_lpr on the second solve (1,313/1,313).
To check leaf i: rebuild `leaf_i.cnf` from prefixes line i and the base body, `xz -d leaf_i.lrat.xz`,
then `cake_lpr leaf_i.cnf leaf_i.lrat`.
