# Third-party material

`k34k33-n19/witness/witness_k34k33_n18.txt` is **not our construction**. It is Steven Van
Overberghe's colouring of K_18 for the cell R(K_{3,4}, K_{3,3}), byte-equivalent to
`K(3,4)K(3,3)n18.g6` in

  https://github.com/Steven-VO/circulant-Ramsey

That repository carries the **GNU General Public License v3.0**. The file is reproduced here
only so that the lower bound can be checked alongside the upper-bound computation in that
directory, which is the part done here. It is cited in Radziszowski's dynamic survey DS1 as
[VO], and appears in House of Graphs as graph 44156 for the companion cell.

The graph itself is the output of his generator rather than the generator's source, and a
Ramsey colouring is arguably a mathematical fact rather than a copyrightable work — but we
make no claim either way. If the author would prefer it removed, linked rather than copied,
or reproduced under different terms, we will do whatever he asks: open an issue or write,
and it will be changed the same day.

Everything else in this repository is our own: the encoder, the checker, the formulas, the
cube decompositions, the ledgers, the K_21 colouring, and the scripts.

`k35k24-n19/witness/witness_k35k24_n18.txt` is **not our construction** either. Its colour-1
graph is byte-equivalent, with the same vertex labels, to `RamseyGraphs/Bipartite/K(3,5)K(2,4)n18.g6`
in the same repository (GPL-3.0). It is reproduced here only so the lower bound can be checked
beside the upper-bound computation in that directory. The omission was pointed out by an
external review on 2026-09-05 (`review/2026-09-05/`); this notice did not acknowledge it before.

`k35k33-n21/witness/witness_k35k33_n20.txt` is a **third case, and a different one**. It is not a
copy of anything: it was found here by a Cayley search on Z_20 (connection set
2,3,4,5,7,10,13,15,16,17,18) and the file is our own output. But its colour-1 graph is
**isomorphic, after relabelling, to `RamseyGraphs/Bipartite/K(3,5)K(3,3)n20.g6`** in the same
repository -- an independent rediscovery of Van Overberghe's graph, not a new object. The lower
bound R(K_{3,5}, K_{3,3}) >= 21 is his and is cited [VO] in DS1; the part done here is the
refutation at n = 21. An external review raised it on 2026-09-11 and the isomorphism is confirmed
here by an explicit relabelling. Nothing in this repository claimed the colouring as new, but the
directory README said his colouring was "not deposited here" while a colouring of K_20 sat in
`witness/`, which invited exactly that reading. Corrected.

All 33 deposited witnesses were checked against every graph in his Bipartite directory on
2026-09-11. Three coincide -- the two above that are byte-identical copies, and this one, which is
isomorphic with different labels. The other thirty match nothing in his archive.

