# One worked subcube

`leaf1.lrat` is the refutation of subcube 1, checked by `lrat-check`. It is included so a
reader can verify one piece of the upper bound without regenerating all 571.

The formula it refutes is not shipped, because it is derivable: take
`../instance/k34k33_n19.cnf`, add the literals of the first `a` line of
`../instance/k34k33_n19_d10.icnf` as unit clauses, and adjust the header count. That is
what `../reconstruct.sh` does for every subcube. To rebuild and check just this one:

```sh
cd ..
B=instance/k34k33_n19.cnf; I=instance/k34k33_n19_d10.icnf
NV=$(awk '/^p cnf/{print $3;exit}' $B); NC=$(awk '/^p cnf/{print $4;exit}' $B)
lits=$(grep '^a ' $I | sed -n 1p | sed 's/^a //; s/ 0$//'); nl=$(wc -w <<<"$lits")
{ echo "p cnf $NV $((NC+nl))"; for l in $lits; do echo "$l 0"; done
  grep -v '^c' $B | grep -v '^p cnf'; } > /tmp/leaf1.cnf
lrat-check /tmp/leaf1.cnf sample/leaf1.lrat        # expect: c VERIFIED
```

The other 570 certificates are the same shape. Together they total roughly 12 GB, which is
why only this one is here.
