"""Recover the complete [clause, permutation] entries from a --sym-break-clauses dump that was
truncated (smsg killed by a timeout mid-write). Each entry is independently a valid non-canonicity
certificate, so a prefix of them is still sound -- it simply prunes less. Parses incrementally with
a bracket-depth scan rather than json.load, which would reject the whole file."""
import json, sys
raw = open(sys.argv[1]).read()
key = '"sym_clauses":'
i = raw.index(key) + len(key)
while raw[i] in ' \n\t': i += 1
assert raw[i] == '[', raw[i]
i += 1
out, depth, start = [], 0, None
for j in range(i, len(raw)):
    c = raw[j]
    if c == '[':
        if depth == 0: start = j
        depth += 1
    elif c == ']':
        depth -= 1
        if depth == 0:
            try: out.append(json.loads(raw[start:j+1]))
            except Exception: pass
json.dump({"sym_clauses": out}, open(sys.argv[2], "w"))
print(f"salvaged {len(out)} complete entries from {len(raw)/1e6:.1f} MB -> {sys.argv[2]}")
