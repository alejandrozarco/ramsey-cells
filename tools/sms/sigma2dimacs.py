import json, sys
# smsg --sym-break-clauses dumps {"sym_clauses": [ [clause, permutation], ... ]} where a clause is a
# list of [sign, u, v] literals over EDGE variables named by their 0-based vertex pair, and the
# permutation is the non-canonicity witness for that clause. Here we only need the clause; the
# permutation is what the nc-checker validates separately.
n = int(sys.argv[2])
def eidx(u, v):                      # row-major upper triangle, 1-based DIMACS var
    if u > v: u, v = v, u
    return sum(n - 1 - i for i in range(u)) + (v - u - 1) + 1
d = json.load(open(sys.argv[1]))["sym_clauses"]
out = []
for clause, perm in d:
    lits = []
    for s, u, v in clause:
        lits.append(s * eidx(u, v))
    out.append(lits)
with open(sys.argv[3], "w") as f:
    for c in out:
        f.write(" ".join(map(str, c)) + " 0\n")
print(f"{len(out)} sigma clauses -> {sys.argv[3]}; max var {max(abs(l) for c in out for l in c)}, "
      f"edge vars for n={n} are 1..{n*(n-1)//2}")
