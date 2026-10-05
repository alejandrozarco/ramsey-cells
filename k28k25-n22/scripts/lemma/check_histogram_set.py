#!/usr/bin/env python3
"""Check the census denominator at both levels it is built from.

LEVEL 1 -- the 44 histograms.  Lemma12.lean proves that for any colouring of K22 with blue
codegree <= 4 and red codegree <= 7, the pair (n8, n10) lies in
`admissibleHistograms = { (a,b) : a < 8, b < 11, (a+b) even }`, and that this set has exactly
44 elements (`admissibleHistograms_card`, by `decide`).  This script rebuilds that set from the
same three bounds Lean proves -- n8 <= 7 (`n8_le_seven`), n10 <= 10 (`n10_le_ten`), n9 even
(`histogram_membership`) -- and compares it with the histograms the census actually covers.

LEVEL 2 -- the 781 rooted lists (obligation G, combinatorial half).  Each histogram is expanded
into (root degree, composition) cases by the generator's own rule:

    root degree k  =  8 if n8 > 0, else 10 if n10 > 0, else 9
    compositions   =  all (i, j, l) with i + j + l = k and 0 <= x_d <= n_d - [k == d+8]

the bracket subtracting the root itself from its own degree class.  This script re-derives that
expansion and checks the list files on disk are exactly it: no case missing, none extra.

Both sides are read off the FILENAMES of the `H_*.txt` list files, which are the census's own
denominator.  It does not consult `gen_manifest.json`: that file is written by whichever
regeneration run produced it and can be partial (it held 20 of 781 cases when this was written),
so trusting it would silently shrink the denominator.  Nor does it use ledgers, which exist only
for lists already worked on and would shrink the denominator as a function of progress
(CLAUDE.md rule 1).

WHAT THIS CHECKS AND WHAT IT DOES NOT.  This compares FILENAMES.  It establishes that the set of
case labels on disk is exactly the set the rule requires -- no case missing, none extra, none
misnamed.  It says nothing whatever about the CONTENTS of those files: 781 empty files with the
right names pass it, by design.  Content completeness is a different obligation, discharged by the
independent enumeration (`scripts/lemma/indep_check.py`, 53/53 families) and by
`scripts/lemma/case_inventory.py`, which also validates each `gen_*.json`'s parameters against its
filename and its cube count.  Run those too; this is not a substitute for either.

The comparison is by GENERATED CANONICAL NAME, not by parsing what is on disk.  An earlier version
parsed each filename with an unanchored regex and collected the results into a set, and Astra round
37 broke it three ways: `H_00_22_0_r9_c090.txt` (a leading-zero alias) and
`H_junk_H_0_22_0_r9_c090.txt` (a prefixed name) were both accepted as the case they alias, and
because the results were de-duplicated into a set, an alias could REPLACE the canonical file
entirely and the run still printed "781 rooted lists" and exited 0 -- while any downstream tool
building the canonical path would fail.  Generating the expected names and comparing them to the
actual basenames cannot fail that way: a name is either the one the rule produces or it is not.

Exits 1 on any mismatch, 2 if it found no list files (so a wrong directory cannot pass silently).

Usage:  python3 scripts/lemma/check_histogram_set.py [--census-dir runs/k28_rooted]
"""
import argparse
import collections
import os
import re
import sys
from glob import glob

N = 22
N8_MAX = 7    # Lemma12.lean : n8_le_seven
N10_MAX = 10  # Lemma12.lean : n10_le_ten
# Anchored at both ends on the BASENAME. Used only to spot files that are list-shaped but not
# canonical, so they can be reported rather than silently ignored.
LISTISH = re.compile(r"\AH_.*\.txt\Z")


def admissible_histograms():
    """Lean's `admissibleHistograms`, rebuilt from the three proved bounds.

    n9 even is equivalent to n8 + n10 even, since the three sum to 22.
    """
    return {(n8, n10)
            for n8 in range(N8_MAX + 1)
            for n10 in range(N10_MAX + 1)
            if (n8 + n10) % 2 == 0}


def root_degree(hist):
    """The generator's root rule, from rooted_gen_lists.py."""
    n8, _n9, n10 = hist
    return 8 if n8 > 0 else (10 if n10 > 0 else 9)


def compositions(hist, k):
    """Every admissible (i, j, l): sums to k, and class d supplies at most n_d, less the
    root itself when the root is in class d."""
    return {(i, j, k - i - j)
            for i in range(k + 1)
            for j in range(k - i + 1)
            if all(0 <= x <= hist[d] - (1 if k == d + 8 else 0)
                   for d, x in enumerate((i, j, k - i - j)))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--census-dir", default="runs/k28_rooted",
                    help="directory holding the H_*.txt rooted-list files")
    args = ap.parse_args()
    rc = 0

    lean = admissible_histograms()
    if len(lean) != 44:
        print(f"FAIL: rebuilt admissible set has {len(lean)} elements, expected 44")
        return 1

    # Build the canonical name of every case the rule requires. The tag format is
    # H_<n8>_<n9>_<n10>_r<k>_c<i><j><l>.txt, the composition digits concatenated with no separator.
    expected = {}
    for n8, n10 in sorted(lean):
        hist = (n8, N - n8 - n10, n10)
        k = root_degree(hist)
        for comp in sorted(compositions(hist, k)):
            name = (f"H_{hist[0]}_{hist[1]}_{hist[2]}_r{k}"
                    f"_c{comp[0]}{comp[1]}{comp[2]}.txt")
            if name in expected:
                print(f"FAIL: the naming scheme is ambiguous -- {name} is produced by both "
                      f"{expected[name]} and {(hist, k, comp)}")
                rc = 1
            expected[name] = (hist, k, comp)

    actual = {os.path.basename(p) for p in glob(os.path.join(args.census_dir, "H_*.txt"))}
    if not actual:
        print(f"FAIL: no H_*.txt list files under {args.census_dir} -- nothing was checked")
        return 2

    for name in sorted(expected.keys() - actual):
        hist, k, comp = expected[name]
        print(f"FAIL: missing {name}  (hist {hist}, root {k}, composition {comp})")
        rc = 1
    for name in sorted(actual - expected.keys()):
        why = "not a case the root/composition rule produces"
        if not LISTISH.match(name):
            why = "does not even match H_*.txt"
        print(f"FAIL: unexpected {name}  ({why})")
        rc = 1

    # The histogram line is implied by the above, but report it separately: it is the half that
    # is tied to Lean, and a referee should be able to see it pass or fail on its own.
    hist_expected = {(n8, n10) for n8, n10 in lean}
    hist_actual = set()
    for name in actual & expected.keys():
        h = expected[name][0]
        hist_actual.add((h[0], h[2]))
    for h in sorted(hist_expected - hist_actual):
        print(f"FAIL: Lean admits histogram n8={h[0]} n10={h[1]}, which the census omits entirely")
        rc = 1

    if rc == 0:
        print(f"OK: {len(hist_actual)} histograms == {len(lean)} admitted by Lemma12.lean")
        print(f"OK: {len(actual)} list filenames == {len(expected)} required by the "
              f"root/composition rule")
        print(f"    exact name-by-name match under {args.census_dir}; nothing missing, "
              f"nothing extra")
        print("    NOTE: this compares filenames only. It does NOT check the files' contents --")
        print("          781 empty files with the right names would pass. For content, run")
        print("          scripts/lemma/indep_check.py and scripts/lemma/case_inventory.py.")
        ledgers = len(glob(os.path.join(args.census_dir, "ledger_*.jsonl")))
        print(f"    (information only, not part of the check: {ledgers} of those "
              f"{len(actual)} lists have a ledger)")
    return rc


if __name__ == "__main__":
    sys.exit(main())
