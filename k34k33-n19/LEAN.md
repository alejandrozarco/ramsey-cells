# Rebuilding the Lean theorem

```sh
bash lean/rebuild.sh [workdir]
```

That regenerates everything and ends with the theorem

```
theorem base_unsat : base.Unsat
```

where `base = parseDimacs "<contents of instance/k34k33_n19.cnf>"` — the formula is embedded
in the statement, so the theorem is about exactly the shipped file. The build prints
`#print axioms base_unsat`, which should match `AXIOMS.txt`: `propext`, `Classical.choice`,
`Quot.sound`, 572 `native_decide`, no `sorryAx`.

## What it needs

`git`, [`elan`](https://github.com/leanprover/elan), and on `PATH`:

| tool | note |
|---|---|
| `cadical` >= 3 | run with `--no-factor`, which the script passes; factoring adds extension variables the checker rejects |
| `lrat-trim` | <https://github.com/arminbiere/lrat-trim> |
| `lrat-check` | from <https://github.com/marijnheule/drat-trim> |

Pinned: `leanprover/lean4:v4.30.0` (lrat-catcher's `lean-toolchain`), lrat-catcher at
commit `4ec2168`, CaDiCaL 3.0.1.

## Cost, and the one hard limit

Refuting the 571 subcubes takes about 2.4 CPU-hours. The Lean build is longer.

The composing step imports one module per subcube — roughly 16 GB of `.olean`.

**Correction (2026-08-30): the 16 GB failure was not the composing step.** On a 16 GB machine
the composing step (`Main`) builds in about a minute once every chunk is present; what fails is
building the largest chunk. `Chunk533` (1587 MB of source) has a **measured peak RSS of
20.8 GB**, so it cannot be elaborated in 16 GB, and lake will silently attempt exactly that
whenever it judges the module stale. Two earlier "composing failures" were that rebuild
misattributed. Chunks up to 1218 MB do build in 16 GB, though they dip the disk to ~3 GB —
macOS grows swap on the data volume, so a memory blowup presents as a disk crisis.

The practical route on a small machine: build the one oversized chunk elsewhere and transplant
its artifacts. **Lean oleans are byte-identical across x86_64-linux and arm64-darwin** (verified
by md5 on a shared module), so this works — but a module has artifacts in *two* trees, and
copying only the first makes lake rebuild it:

| tree | files |
|---|---|
| `.lake/build/lib/lean/<mod path>/` | `.olean`, `.ilean`, `.olean.hash`, `.ilean.hash`, `.trace` |
| `.lake/build/ir/<mod path>/` | `.c`, `.c.hash`, `.setup.json` |

`Chunk533.c` is 1465 bytes; omitting it triggers the full 1.5 GB rebuild. Verify a transplant
with `lake build <module>:olean --no-build`, which reports staleness without building anything.

Related:
`chunkSize` must stay at 1. A module whose embedded certificate pushes its `.olean` past
about 2 GB builds fine but cannot afterwards be imported.

## What the script does

1. clones and builds lrat-catcher at the pinned commit;
2. `lratcatch-export` splits the formula by the cube file into `export/leaf1.cnf` …
   `export/leaf571.cnf`, plus `export/negcubes.cnf`, the conjunction of the negated cubes;
3. refutes `negcubes.cnf` to rebuild `cover.lrat`, checks it, and compares against the
   shipped `instance/cover.lrat`;
4. refutes and checks each of the 571 subcubes, writing `proofs/leaf_<i>.lrat`;
5. `lratcatch-cover-parallel` emits one Lean module per subcube plus `Base`, `Cover` and
   `Main`;
6. builds the chunks, then composes `Main`.

Nothing in it trusts the certificates shipped here; step 3 rebuilds the cover rather than
reading ours. `lean/` holds `Base.lean`, `Cover.lean`, `Main.lean` and one chunk module
already, so the statement and the composition can be read without running any of this.
