# SMS route: symmetry clauses extracted once, then our ordinary certified pipeline

Status 2026-09-08: prototype PASSED on R(K_{3,4},K_{3,3}) = 19 at n=19, twice, and every symmetry
clause is machine-checked by the same verified checker that carries our leaf proofs. Not yet used for
any deposited result. Nothing here is a claim.

## The idea

SAT modulo symmetries (Kirchweger and Szeider) does complete symmetry breaking with a propagator
inside the solver. We do NOT run the propagator at proof time. We run `smsg` once with
`--sym-break-clauses` to dump the symmetry clauses Sigma it learned, append Sigma to the formula, and
solve with stock CaDiCaL. Consequences:

* leaves are ordinary DIMACS with ordinary LRAT proofs, so lrat-trim, lrat-check, cake_lpr and the
  Comparator replay all still apply, unchanged;
* smsg's own `--lrat-output` is NOT used, and must not be: it emits proofs citing clause ids that were
  never introduced, which lrat-check rejects.

## Measured, on the cell we had already closed

| route | cubes | core-s | leaves lrat-check | cake_lpr sampled |
|---|---|---|---|---|
| deposited (`runs/certify_k34k33_n19.jsonl`) | 571 | 2,486 | - | - |
| SMS, formula keeps our static vertex-lex | 161 | 216 | 161/161 | 25/25 |
| SMS, isomorphism-closed formula (no static lex) | 335 | 292 | 335/335 | 25/25 |

Both SMS runs answer UNSAT and both pass the canary below. **Use the isomorphism-closed variant**: it
costs 35% more than the other and is still 8.5x cheaper than the deposited route, and it removes a
real soundness question (see below).

## The soundness question, and why the no-lex variant is the answer

SMS's argument requires the base formula to be closed under isomorphism. Our usual formula is NOT: it
already carries static vertex-lex breaking. Appending Sigma to it is sound only if the two canonical
forms coincide exactly — same pair order, same colour orientation, same min/max sense. That happens to
hold for the clause families we decoded, but the aux-encoded part rests on a comment in `tosms.py`
rather than a check. Generating the formula WITHOUT `--vertex-lex` removes the question entirely,
because the codegree constraints alone are isomorphism-invariant.

## Non-negotiable canary

Every run begins by pushing the known-SATISFIABLE neighbour (n = 18 here, since R = 19) through the
whole pipeline and asserting SAT. If it ever returns UNSAT the conversion orientation is wrong and
every result behind it is void. This is a control, not a proof, and it is cheap.

## Validating Sigma

Each Sigma clause comes with a permutation that is meant to witness non-canonicity. Validating those
witnesses is the only new obligation the route adds.

* `nc_sat_reduction.py` turns each obligation into a propositional refutation: UNSAT means the witness
  is valid over ALL completions of the partial assignment, not merely over sampled ones.
* `nc_cake_check.py` solves each with CaDiCaL, trims, and checks with **cake_lpr**. Results:
  n=19 **2,950 / 2,950 VERIFIED, 0 failures, 56 s** (`runs/cake_nc_ledger.jsonl`);
  n=21 **46,996 / 46,996 VERIFIED, 0 failures, 18 min** (`runs/cake_nc21_ledger.jsonl`).

  **What that does and does not establish.** cake_lpr checks each obligation individually: for clause
  C with witness pi, no completion of the assignment C forbids can be canonical. It does NOT check
  the step from "every clause is individually valid" to "appending all of Sigma preserves
  satisfiability of the original formula". That composition is a mathematical argument we assert, not
  a checked one, so **"cake_lpr-verified symmetry breaking" would be an overclaim** and must not be
  written. The correct sentence today is: each nc-obligation is machine-checked by a verified checker;
  their composition into the soundness of the append is argued, not checked.

  Closing that properly is one Lean lemma, not a re-proof of the encoder: the lex-minimum of the
  isomorphism-closed set of valid colourings satisfies every clause whose certificate checks. Because
  Sigma clauses mention only edge variables, this does NOT require the Lean front end to emit the
  one-var-per-edge formula, so the "weeks" estimate recorded on 2026-09-08 applies to a route we are
  not taking. Kirchweger, Manrique and Szeider (IJCAR 2026, artifact `leansms`) have done the
  corresponding lemma for their setting.
* `checker_A.py` and `checker_C.py` are independent direct decision procedures kept as cross-checks.
  Four independent implementations agreed on all 2,950 clauses and on 21,925 adversarial instances,
  including an exhaustive comparison against brute force over all 17,472 cases at n = 4.

Convention that matters: apply the permutation forward, (pi.G)(u,v) = G(pi(u),pi(v)). The inverse
convention passes 1,021 of 2,950 clauses, which looks like a partial failure rather than a wrong
convention, because 964 of the witnesses are involutions.

## Scope

Two colours only. Canonicity is defined on a single binary adjacency matrix and smsg refuses to export
symmetry clauses for multi-colour problems, so the three-colour and five-colour cells get nothing from
this, ever.
