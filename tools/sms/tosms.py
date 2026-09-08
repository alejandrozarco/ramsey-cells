import sys
# gen_ramsey layout (r=2): var(e,c) = eidx[e]*2 + c, eidx row-major upper triangle.
# SMS layout: edge vars 1..E in the SAME row-major order, TRUE = edge present.
# We map colour 2 -> edge present (bit 1), colour 1 -> non-edge (bit 0), so that
# gen_ramsey's vertex-lex (values 1<2, valseq(x) <=lex valseq(x o s)) is exactly
# SMS's lex-MINIMAL adjacency matrix.
inf, outf, E = sys.argv[1], sys.argv[2], int(sys.argv[3])
out=[]; nv=0
for line in open(inf):
    if line.startswith('c'): continue
    if line.startswith('p'):
        nv = int(line.split()[2]); continue
    lits=[int(x) for x in line.split()[:-1]]
    new=[]
    for l in lits:
        a=abs(l); s=1 if l>0 else -1
        if a<=2*E:
            k=(a-1)//2; c=(a-1)%2+1      # edge index k (0-based), colour c
            m = (k+1) if c==2 else -(k+1)  # colour2 -> positive edge var
            new.append(s*m)
        else:
            new.append(s*(a-2*E+E))       # aux vars shift down by E
    st=set(new)
    if any(-x in st for x in st): continue  # tautology (ALO/AMO become these)
    out.append(sorted(set(new), key=abs))
nvnew = nv-2*E+E
with open(outf,'w') as f:
    f.write(f"p cnf {nvnew} {len(out)}\n")
    for c in out: f.write(" ".join(map(str,c))+" 0\n")
print(f"{outf}: {nvnew} vars, {len(out)} clauses (was {nv}/{sum(1 for _ in open(inf) if not _.startswith(('c','p')))})")
