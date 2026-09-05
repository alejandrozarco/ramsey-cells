# For a reviewer: how to check what this repository contains

Every statement below names the file that backs it. Tool versions are the ones used here; a
reviewer may substitute newer ones at their own judgement.

## 1. Colorings (lower bounds)

A file `witness_*.txt` lists every edge of K_n with a color. To check it contains none of the
forbidden subgraphs:

```
python3 tools/check_any.py <witness file> <cell spec>      # e.g. K3x5,K2x5
```

`tools/check_any.py` is written from the definitions (bipartite patterns and books by codegree;
cliques, cycles, wheels and K_4-e by embedding) and shares no code with the encoder. A second,
independent checker is `bench.html` (paste the coloring). Both are in this repository.

## 2. Refutations (upper bounds): the cube tree

A refutation directory (`k34k33-n19/`, `k35k24-n19/`, `k35k25-n22/`) holds:

* the instance CNF — produced by `tools/gen_ramsey.py <n> <cell> --vertex-lex` (the encoder is at the
  repository root under `tools/`; the cell directories carry their own copies);
  regenerate it and `diff` (ignoring `c`/`p` lines) to confirm.
* `instance/*_d10.icnf` — the top-level cubes (march_cu, `-d 10`), and `tree/splits/<id>_d8.icnf`
  — the sub-cubes of every cube that hit the time cap. A leaf's CNF is the instance plus one unit
  clause per literal of the leaf's cube (units first, then the instance).
* `tree/ledger.jsonl` — one row per cube: `id`, `result`, `secs`, and `verified`, which is `true`
  only if the LRAT proof produced by CaDiCaL was accepted by `lrat-trim` (exit 20) and then
  `lrat-check` (exit 0, no "failed") at solve time. Older rows have their verification in
  `tree/verified_leaves.jsonl`.
* `tree/cover_audit_*.txt` — output of `tools/verify_close.py <cnf> <top icnf> <tree dir>`. It walks
  the cube tree ON DISK (top cubes, then `splits/`), never the ledger, and reports TREE CLOSED only if
  every leaf has a checked UNSAT verdict and none is SAT; it then writes the conjunction of the negated
  leaves as a CNF, refutes it with CaDiCaL and checks the LRAT proof (lrat-trim, lrat-check), and
  reports COVER VERIFIED. Both are needed: an external review (2026-09-05) showed the earlier tool,
  which did only the first, accepted a satisfiable formula with an incomplete cube list. Re-run it;
  it needs `cadical`, `lrat-trim` and `lrat-check` (paths via `CADICAL`, `LRAT_TRIM`, `LRAT_CHECK`).
  `k34k33-n19/` predates this layout: its 571 cubes are all top-level and its cover proof is the
  `cover` row of its cake_lpr ledger.

Proof files are not deposited (hundreds of GB); the verdicts are re-derivable per leaf (§3).

## 2a. What each refutation directory actually contains

`k34k33-n19/`:
  top level: AXIOMS.txt, LEAN.md, README.md, SHA256SUMS, reconstruct.sh
  lean/: 9 files (e.g. Base.lean, Chunk232.lean, Cover.lean, EncodedUnsat.lean, Encoder.lean, EncoderBridge.lean, …)
  ledger/: 1 files (e.g. k34k33_certify_ledger.jsonl)
  witness/: 3 files (e.g. coloring.svg, matrix.txt, witness_k34k33_n18.txt)
  tools/: 2 files (e.g. check_ramsey.py, gen_ramsey.py)
  certificate/: 9 files (e.g. CERTIFICATE.md, ComparatorAxioms.lean, ComparatorChallenge.lean, ComparatorCubes.lean, ComparatorUnsatFallback.lean, PASS_lrat-catcher_2026-09-03.log, …)
  instance/: 3 files (e.g. cover.lrat, k34k33_n19.cnf, k34k33_n19_d10.icnf)
  sample/: 2 files (e.g. README.md, leaf1.lrat)

`k35k24-n19/`:
  top level: README.md
  tree/: 3 files (e.g. cover_audit_2026-09-05.txt, k35k24_n19_flat.icnf, ledger.jsonl)
  tree/splits/: 2 files (e.g. 251_d8.icnf, 258_d8.icnf)
  ledger/: 2 files (e.g. LIVE_k35k24_19_ledger.jsonl, k35k24_straggler240_ledger.jsonl)
  witness/: 3 files (e.g. coloring.svg, matrix.txt, witness_k35k24_n18.txt)
  certificate/: 10 files (e.g. CERTIFICATE_k35k24.md, ComparatorAxiomsK35K24.lean, ComparatorChallengeK35K24.lean, ComparatorCubesK35K24.lean, ComparatorUnsatK35K24.lean, PASS_lrat-catcher-k35k24_2026-09-05.log, …)
  instance/: 2 files (e.g. k35k24_n19.cnf, k35k24_n19_d10.icnf)

`k35k25-n22/`:
  top level: README.md
  tree/: 5 files (e.g. close_k35k25_n22.log, cover_audit_2026-09-05.txt, k35k25_n22_flat.icnf, ledger.jsonl, verified_leaves.jsonl)
  tree/splits/: 674 files (e.g. 182_d8.icnf, 184_d8.icnf, 185.60_d8.icnf, 185_d8.icnf, 208_d8.icnf, 225_d8.icnf, …)
  certificate/: 19 files (e.g. ComparatorAxiomsK35K25.lean, ComparatorChallengeK35K25.lean, ComparatorCubes.lean, ComparatorCubesK35K25.lean, ComparatorUnsatK35K25.lean, Encoder.lean, …)
  instance/: 2 files (e.g. k35k25_n22.cnf, k35k25_n22_d10.icnf)

## 3. Leaf verdicts by an independent, verified checker

`certificate/cake_lpr_ledger*.jsonl` records, per leaf: the sha256 of the leaf DIMACS that was
checked, the solver verdict, the verdict of `cake_lpr` (`s VERIFIED UNSAT`), and proof size.
`cake_lpr` is the CakeML-verified LRAT checker (github.com/tanyongkiam/cake_lpr @ a36874a, built
from its shipped assembly with `make`). To re-derive any leaf's verdict:

1. Rebuild the leaf DIMACS. Either concatenate the instance with the cube's unit clauses as in §2,
   or print it from the Lean encoder term (§4): `lake exe lratcatch-export-encoder <cell> <flat icnf> <dir> --sample N`.
   Its sha256 must equal the ledger entry (for `k35k25-n22` the leaves were printed as
   header + unit lines by the same program with `--prefixes`; `certificate/sample_leaf0_lean_printed.cnf`
   is one full leaf as printed).
2. `cadical --lrat --binary=false leaf.cnf leaf.lrat` (CaDiCaL 3.0.1), then `cake_lpr leaf.cnf leaf.lrat`.

`tools/cert_pass.py` is the script that produced these ledgers.

## 4. The statement, checked by Comparator

`certificate/` holds a Lean 4 challenge/solution pair and a JSON configuration for
[leanprover/comparator](https://github.com/leanprover/comparator). The transcript
`certificate/PASS_*.log` ends with `Your solution is okay!` and lists the axioms the theorem
depends on: `propext`, `Quot.sound`, `Classical.choice`, and the two named external verdicts
declared in `certificate/ComparatorAxioms*.lean` (every leaf UNSAT; the negated cubes UNSAT),
which §3 re-derives. To reproduce:

```
git clone https://github.com/leansolving/lrat-catcher && cd lrat-catcher && git checkout 23a251d3aae3
cp <this dir>/certificate/*.lean LRATCatcher/       # Encoder, ComparatorCubes*, ComparatorAxioms*, ComparatorChallenge*, ComparatorUnsat*, K35K25FlatIcnf* as present
cp <this dir>/certificate/ExportEncoder.lean .      # and add its lean_exe entry to lakefile.toml (see the file header)
# Lean v4.30.0 (lean-toolchain); comparator @ 71b52ec, lean4export @ v4.30.0, nanoda_lib @ 68d5ca9, landrun @ 5ed4a3d — build as in lean-eval's instructions
lake env <path>/comparator certificate/<cell>.json
```

Comparator builds the challenge in a sandbox, exports both environments, replays the solution
in the Lean kernel and in nanoda, and checks that the theorem statements and the permitted
axioms match the challenge file.

## 5. What the statement does and does not say

The certified theorem is that the CNF built by `LRATCatcher.Encoder.<cell>` — a Lean
transcription of `tools/gen_ramsey.py` — is unsatisfiable. That it equals the deposited instance
is checked by `diff` (§2). That its unsatisfiability implies no coloring exists (faithfulness of
the codegree/Sinz encoding and soundness of the lex-leader symmetry breaking) is proved in a
separate Lean development, `sbsound`, not public at the time of writing; the transcripts of its
own Comparator check (three standard axioms only) can be provided on request.

## 6. External review

`review/2026-09-05/` holds an external review of commit 784339a (produced by a GPT-based reviewer
run by the author, with its own standard-library witness checker and artifact audit). Its findings
led to the corrections in commit history after that date: the second witness attribution in
`NOTICE.md`, the cover-completeness check in `tools/verify_close.py`, the root `tools/gen_ramsey.py`,
the deposited K_{3,5}/K_{2,4} instance and tree, and this section.

## Tool versions used

CaDiCaL 3.0.1 · march_cu (github.com/marijnheule/CnC @ 705b60c) · lrat-trim 0.2.0 (@ b30f400) ·
drat-trim/lrat-check @ 2e3b2dc · cake_lpr @ a36874a (binary sha256 prefix 1822ca1e5d0f925e) ·
Lean 4.30.0 · comparator @ 71b52ec · lean4export @ v4.30.0 · nanoda_lib @ 68d5ca9 · landrun @ 5ed4a3d.
