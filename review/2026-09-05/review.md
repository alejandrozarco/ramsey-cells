# Review of ramsey-cells

Reviewed 5 September 2026 at commit [784339a6b3ffb1b2a3f84c4c3c3e24d45436a67e](https://github.com/alejandrozarco/ramsey-cells/tree/784339a6b3ffb1b2a3f84c4c3c3e24d45436a67e). The live checkout contains nine cells; the search engine's cached page was older. No changes were made to the repository.

**Verdict:** all nine deposited colorings pass an independently written checker. Combined with published upper bounds, they establish three exact values and four further lower-bound improvements over DS1.18. Two colorings reproduce prior constructions. The three additional proposed exact values depend on large UNSAT computations that this review has not fully replayed. They should retain that qualification.

This is an artifact and mathematical-claims review, not a completed referee certification or exhaustive priority search. Historical timing, private computations, and every abandoned search in FINDINGS.md were not reproduced.

**Results, cell by cell**

| Ramsey number | DS1.18 baseline | Independently checked here | Verdict |
|---|---|---|---|
| R(K₂,₁₀, K₂,₇) | 29–31 | Valid K₃₀ coloring | **=31**, using published upper bound |
| R(K₂,₁₀, K₂,₆) | 27–29 | Valid K₂₈ coloring | **=29**, using published upper bound |
| R(K₂,₂, K₂,₁₉) | 28–29 | Valid K₂₈ coloring | **=29**, using published upper bound |
| R(K₂,₁₁, K₂,₄) | ≥25 | Valid K₂₅ coloring | **≥26**; general published upper bound gives ≤27 |
| R(K₂,₁₁, K₂,₆) | ≥29 | Valid K₂₉ coloring | **≥30**; general published upper bound gives ≤31 |
| R(K₃,₅, K₂,₅) | 21–23 | Valid K₂₁ coloring | **22–23** established here; proposed =22 needs full refutation replay |
| R(B₅, B₉) | ≥28 | Valid K₂₈ coloring | **29–30**, using published upper bound |
| R(K₃,₄, K₃,₃) | 19–20 | Valid, previously published K₁₈ coloring | **19–20** established here; proposed =19 has substantial computational evidence |
| R(K₃,₅, K₂,₄) | 19–20 | Valid, previously published K₁₈ coloring | **19–20** established here; proposed =19 has substantial computational evidence |

Here Kₐ,ᵦ denotes the complete bipartite graph, and Bₜ means t triangles sharing a spine edge. These are ordinary graph Ramsey numbers on complete graphs, not bipartite-host Ramsey numbers.

Baseline citations: [Radziszowski, Small Ramsey Numbers, revision 18](https://www.cs.rit.edu/~spr/ElJC/sur.pdf), Tables IVb/IVc and §3.3.1(f). The upper bounds 27 and 31 follow by substituting into §3.3.2(j); the book upper bound 30 follows from §5.3(k). The bounds involving K₃,₅ also appear in [Lidický–Pfender, Table 1](https://lidicky.name/pub/ramsey/RamseyA.pdf).

The checker validates every edge exactly once and checks the actual non-induced containment predicate. For Kₛ,ₜ it enumerates every s-set and counts its common neighbors. For Bₜ it considers only same-color spine edges. It imports no repository code. The maximum common-neighbor counts by color were:

| Witness | Maximum counts | Forbidden thresholds |
|---|---|---|
| K₂,₁₀ / K₂,₇ on 30 | 9, 6 | 10, 7 |
| K₂,₁₀ / K₂,₆ on 28 | 9, 5 | 10, 6 |
| K₂,₂ / K₂,₁₉ on 28 | 1, 18 | 2, 19 |
| K₂,₁₁ / K₂,₄ on 25 | 10, 3 | 11, 4 |
| K₂,₁₁ / K₂,₆ on 29 | 10, 5 | 11, 6 |
| K₃,₅ / K₂,₅ on 21 | 4, 4 | 5, 5 |
| B₅ / B₉ on 28 | 4, 8 | 5, 9 |
| K₃,₄ / K₃,₃ on 18 | 3, 2 | 4, 3 |
| K₃,₅ / K₂,₄ on 18 | 4, 3 | 5, 4 |

**What the refutation artifacts actually establish**

| Artifact | K₃,₄ / K₃,₃ at 19 | K₃,₅ / K₂,₄ at 19 | K₃,₅ / K₂,₅ at 22 |
|---|---:|---:|---:|
| Flat cubes | 571 | 773 | 137,350 |
| Successful cake_lpr leaf entries | 571 | 773 | 924 |
| Failed cake_lpr leaf entries | 0 | 0 | 9 |
| Deposited cake_lpr cover verdict | Yes | Yes | No |
| Every recorded input hash independently reconstructed | Yes | Yes | Yes |
| Cover independently proof-checked in this review | Yes | Yes | Yes |
| All leaf proofs replayed in this review | No; one supplied sample passed | No | No |

The first two ledgers have 572 and 774 entries because each includes one cover verdict. They have no duplicate or missing leaf IDs. All their input hashes match formulas reconstructed using the deposited Python encoder and cube lists. This binds the claimed checks to the intended inputs; it does not independently establish that those checks succeeded.

For n=22, an independent tree traversal found 137,350 leaves, no unresolved leaf records, and exact agreement with the flat cube list. Every leaf has a recorded verification flag. The separate cake_lpr pass is much less complete: 933 recorded leaves, 924 successful checks, nine `FAIL:` entries, and no cover entry. Those failure strings do not establish whether proofs were rejected or checker processes failed; their cause is unrecorded.

All three cube covers really are exhaustive. I reconstructed the conjunctions of negated cubes. The deposited K₃,₄/K₃,₃ cover proof passed lrat-check. For the other two covers I generated fresh LRAT proofs with CaDiCaL 3.0.1 and checked them with lrat-check; both passed. The supplied K₃,₄/K₃,₃ leaf proof also passed. These checks prove coverage and that one leaf, not the remaining leaf refutations.

I regenerated the two deposited upper-bound CNFs and obtained identical clause bodies: 105,213 variables/202,770 clauses and 164,416 variables/317,478 clauses. The K₃,₅/K₂,₄ CNF is not deposited as an instance file; reconstruction gives 86,289 variables/165,834 clauses and matches every certificate-ledger hash.

**Findings requiring correction or qualification**

1. **The Comparator results are conditional on external UNSAT assertions.** The [axiom file](https://github.com/alejandrozarco/ramsey-cells/blob/784339a6b3ffb1b2a3f84c4c3c3e24d45436a67e/k35k25-n22/certificate/ComparatorAxiomsK35K25.lean) explicitly assumes both all-leaves-UNSAT and cover-UNSAT; the [solution](https://github.com/alejandrozarco/ramsey-cells/blob/784339a6b3ffb1b2a3f84c4c3c3e24d45436a67e/k35k25-n22/certificate/ComparatorUnsatK35K25.lean) composes those assumptions. Passing Comparator is not itself a proof of them. REVIEWER.md discloses this, and the n=22 README discloses the incomplete second pass. Any summary describing this as a completed end-to-end formal Ramsey proof would exceed the deposited evidence. Publish or replay the external certificates and publish the private encoding/symmetry soundness development to support that stronger description. A formal proof is not mandatory for ordinary mathematics, but its absence limits the formal-certification claim.

2. **The coverage audit can accept an incomplete cover.** [verify_close.py, lines 38–58](https://github.com/alejandrozarco/ramsey-cells/blob/784339a6b3ffb1b2a3f84c4c3c3e24d45436a67e/tools/verify_close.py#L38-L58) checks recorded leaves, without proving that the supplied cubes cover the assignment space. A reproduced example uses base formula ¬x and sole cube x. That leaf is truly UNSAT, but the base remains SAT at x=false. With a verified leaf record, the tool prints `COVER COMPLETE` and exits 0 even with `--check-all`. Require an independently checked negated-cubes refutation, or certified parent-to-child coverage. This is a tool defect; the three actual covers passed the stronger independent checks described above.

3. **A second existing witness is missing from the attribution notice.** Both n=18 colorings match the corresponding files in [Van Overberghe's archive](https://github.com/Steven-VO/circulant-Ramsey/tree/f972741192120565db444cfe88ed3c326ba35982/RamseyGraphs/Bipartite), exactly as labeled graphs, not merely up to isomorphism. NOTICE.md acknowledges K₃,₄/K₃,₃ but then says everything else is the repository author's own. It should also identify `K(3,5)K(2,4)n18.g6`. This proves prior publication of that coloring, not how the current author obtained it. The potentially new contribution for either cell is the upper bound.

4. **The reproduction instructions describe a layout that not all cells have.** [REVIEWER.md, lines 21–34](https://github.com/alejandrozarco/ramsey-cells/blob/784339a6b3ffb1b2a3f84c4c3c3e24d45436a67e/REVIEWER.md#L21-L34) points to root `tools/gen_ramsey.py`, which is absent. Usable copies exist under `k34k33-n19/tools/` and `k35k25-lb22/tools/`. The K₃,₅/K₂,₄ directory has neither the described instance nor tree layout, although its certificate directory has a reconstructible flat cover and complete hash ledger. Its README still points to the older 389+1602 run, whereas the newer certificate uses 773 leaves. Provide cell-specific commands and synchronize these descriptions.

**Novelty assessment**

Seven witnesses improve the quoted DS1.18 lower bounds. Three meet known upper bounds. That is stronger than merely reporting SAT models: their mathematical consequences were independently checked here. It is not proof of worldwide priority as of September 2026.

The two n=18 witnesses are known constructions. The other relevant files currently in Van Overberghe's archive are smaller than the new witnesses for K₂,₁₀/K₂,₇, K₂,₁₁/K₂,₄, K₂,₁₁/K₂,₆, and K₃,₅/K₂,₅. [Wesley's book-Ramsey paper](https://arxiv.org/html/2410.03625v2) does not list a B₅/B₉ improvement among its explicit result tables. Targeted literature searches did not identify a matching earlier improvement, but that negative search is not a novelty certificate.

The final FINDINGS.md note cites a [2024 paper's ≥20 bound](https://arxiv.org/html/2403.20055v1). That is a valid historical result, but the comparison baseline for K₃,₅/K₂,₅ is ≥21, already listed in the earlier Lidický–Pfender table. The root README uses the correct baseline.

**Reproduction files**

`check_witnesses.py` is the independent standard-library checker. `audit_artifacts.py` reconstructs encoder inputs, audits ledger hashes/IDs, and traverses the n=22 tree; it imports the deposited encoder and is not an independent semantic proof of that encoder. Run them with a checkout of the pinned commit:

```sh
python3 check_witnesses.py /path/to/ramsey-cells
python3 audit_artifacts.py /path/to/ramsey-cells /path/to/scratch
```

The accompanying JSON files record witness checks, artifact audits, prior-construction comparisons, the negative control, and actual proof-checker outputs. No full leaf-solver campaign or Lean build was run for this review.
