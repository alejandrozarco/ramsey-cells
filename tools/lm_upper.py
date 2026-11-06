"""Evaluate Lortz-Mengersen (JGT 43 (2003) 252-268) Lemmas 2.2 and 2.3 at given (m, n).

Red is K_{2,m}-free, green is K_{2,n}-free, on K_p.  For one vertex v with red degree a and
green degree b = p-1-a, Lemma 2.3 requires  a*b <= b*(m-1) + a*(n-1);  Lemma 2.2(1) with
t1 = b (green max degree >= b) requires, if b >= n,
    b*C(b-n,2) + (p-b-1)*C(b-n+1,2) <= (m-1)*C(b,2);
Lemma 2.2(2) with t2 = a requires, if a >= m,
    a*C(a-m,2) + (p-a-1)*C(a-m+1,2) <= (n-1)*C(a,2).
If no a in 0..p-1 passes all three, no (K_{2,m},K_{2,n})_p-colouring exists, so R <= p.
Prints the smallest such p and the general bound 2m+2n-3 (Theorem 3.1).
"""
import sys
from math import comb

def ok(p, m, n):
    for a in range(p):
        b = p - 1 - a
        if a * b > b * (m - 1) + a * (n - 1):
            continue
        if b >= n and b * comb(b - n, 2) + (p - b - 1) * comb(b - n + 1, 2) > (m - 1) * comb(b, 2):
            continue
        if a >= m and a * comb(a - m, 2) + (p - a - 1) * comb(a - m + 1, 2) > (n - 1) * comb(a, 2):
            continue
        return True
    return False

def upper(m, n):
    p = 3
    while ok(p, m, n):
        p += 1
    return p

if __name__ == "__main__":
    cells = [(12,3),(12,4),(12,5),(12,6),(12,7),(12,8),(13,3),(13,4),(13,5),(13,6),(13,9),
             (14,3),(14,4),(14,5),(14,6),(14,9),(15,3),(15,4),(15,5),(15,6),(10,6),(10,7),(11,6),(11,4),(8,5)]
    for n, m in cells:
        print(f"R(K2,{n};K2,{m})  lemmas <= {upper(m, n)}   2n+2m-3 = {2*n+2*m-3}")
