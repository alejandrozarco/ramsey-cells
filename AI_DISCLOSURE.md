# AI disclosure

AI models produced the content of this repository: the encoders, checkers, searches, certificates, Lean files,
derived views and text. The repository owner chose the problems, directed the work, ran the computations
and decided on scope and publication. The owner did not check the code, the certificates or the Lean files
line by line.

**Models**
- Claude Opus 5 and Claude Opus 5.5 (Anthropic, via Claude Code) did most of the work, often as several coordinated
  agents. Claude Fable 5.1 (Anthropic) wrote parts of the Lean development and some deposits. The commits carry
  `Co-Authored-By` trailers naming the model.
- Reviews were run as separate read-only instances of these models and of gpt-6-astra (OpenAI, via the Codex CLI).
  The review in `review/2026-09-05/` was run by the owner with an OpenAI GPT model and is reproduced there.

**Reviews.** The AI reviews found real errors, all fixed:
- the K_18 coloring in `k34k33-n19/` is Van Overberghe's and was deposited without attribution (`NOTICE.md`);
- `tools/verify_close.py` accepted an incomplete cube list in a negative control; it now also refutes the negated
  leaves with a checked proof, and every deposited cover was re-verified;
- `REVIEWER.md` gave wrong encoder paths and per-cell layouts, and one refutation was deposited without its instance
  and cube tree;
- results presented as new that were not: the K_20 in `k35k33-n21/` is Van Overberghe's graph rediscovered, and the
  upper bound in `k211k25-n28/` follows from Lortz and Mengersen's lemmas.

Defects found in the tooling itself, including a search recorded as a refutation when it was about 15% finished, are
listed in [`FINDINGS.md`](FINDINGS.md), section 6.

AI reviews are not peer review, and no human expert has checked this work. For the refutations this repository is a
*warrant*, not a human-readable proof (see the note at the top of `README.md`).

**What is checked by software**
- Colorings: `tools/check_any.py` and `bench.html`, written from the definitions and sharing no code with the
  encoder, check that a deposited coloring avoids both subgraphs.
- Refutations: every leaf of a cube tree was solved by CaDiCaL with an LRAT proof accepted by `lrat-trim` and
  `lrat-check`; `tools/verify_close.py` checks from the files on disk that the leaves cover the instance, with its own
  checked proof. Where a cell's `certificate/` says so, the leaves and the cover were re-checked by cake_lpr, a
  CakeML-verified LRAT checker.
- Lean 4 and Comparator: where a cell carries a Comparator transcript, the kernel and nanoda accept the statement
  with the axioms that transcript lists. For `k34k33-n19/`, `k35k25-n22/`, `k211k24-n26/`, `k211k23-n22/` and `k35k24-n19/`
  the encoding step and the value as one theorem about colorings are also checked (the cells' `certificate/faithful/`), using `lean/sbsound/`.

What remains to be trusted:
- that each encoder states "a coloring avoiding both subgraphs exists" and nothing stronger, and that its symmetry
  breaking is sound; this is machine-checked (`lean/sbsound/`) and composed with the refutation for the five cells above, and is otherwise the code as reviewed;
- the named external axioms in each `certificate/` (the cake_lpr or LRAT verdicts on the files printed from the Lean
  terms), and the checkers that produced them;
- that the Lean statement files express the intended theorems, and the Lean kernel and toolchain;
- the SAT and proof-checking tools as built from the versions in `REVIEWER.md`.
