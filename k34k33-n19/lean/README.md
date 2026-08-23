# The Lean modules

These are the parts of the Lean development that carry meaning rather than bulk.

| file | what |
|---|---|
| `Base.lean` | `def base : CNF Nat := parseDimacs "..."` — the formula, embedded verbatim. This is what the theorem is *about*. |
| `Cover.lean` | `theorem coverThm : (negCubesCNF cubes).Unsat` — the cubes leave nothing uncovered. |
| `Main.lean` | `theorem base_unsat : base.Unsat` — composes the 571 chunk theorems with `coverThm`, and ends with `#print axioms base_unsat`. |
| `Chunk232.lean` | one leaf module, included so the shape is visible. It is the smallest of the 571. |

The other 570 chunk modules are not here. Each embeds its subcube's LRAT certificate as a
string literal, and together they run to about 16 GB; the largest single one is 1.7 GB.
`../LEAN.md` gives the commands to regenerate them.

`Main.lean` is the file to read first. Its proof term is one long nested application of
`List.forall_mem_append.mpr` gathering `chunk1_ok` through `chunk571_ok`, then
`LRATCatcher.cover_unsat` applied to that and to `coverThm`. Nothing else happens in it —
the mathematical content is entirely in the statement (`Base.lean`) and in the combinator,
which is proved inside lrat-catcher rather than here.

`../AXIOMS.txt` is the output of that `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound`, and 572 `native_decide` axioms, one per chunk plus one for the cover. No
`sorryAx`.
