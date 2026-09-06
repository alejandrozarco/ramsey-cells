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
whose printed CNF is byte-identical to `instance/k211k23_n22.cnf`, sha256 57518b8c...), its two external
verdict axioms discharged by cake_lpr (leaves and cover), the cake_lpr ledger and the PASS transcript.

The refutation needs the encoding to be faithful, the symmetry breaking to be sound, and the cube cover
to be exhaustive. The cover is machine-checked (above). The encoding and the vertex-lex symmetry
breaking are argued in the private Lean development described in `../REVIEWER.md` section 5; the
public chain ends at "this CNF is unsatisfiable".

Method note: the same cell under the degree-ordering formula of `k28k25-n22/` measured about twenty
times more expensive in a sampled cube protocol (see `../FINDINGS.md`, 2026-09-06); the deposited
encoding was used for that reason.

## Check

```
python3 ../tools/verify_close.py instance/k211k23_n22.cnf instance/k211k23_n22_d10.icnf tree --check-all
```
(`tree/` carries the ledger with verified verdicts; proofs were deleted after checking, so a third
party re-solves each leaf: `../tools/cert_pass.py` does that from the Lean-printed prefixes and checks
every proof with cake_lpr.)
