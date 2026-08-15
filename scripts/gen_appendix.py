import sympy as sp, itertools
from collections import defaultdict

Z, Zb, X, W, Wb = sp.symbols(r'\zeta \bar{\zeta} x w \bar{w}', commutative=True)

def conj(p): return p.xreplace({Z:Zb, Zb:Z, W:Wb, Wb:W})
def cmul(p,q):
    z1,z2 = p; z3,z4 = q
    return (sp.expand(z1*z3 - z2*conj(z4)), sp.expand(z1*z4 + z2*conj(z3)))
GEN = {'a':(Z,sp.Integer(0)), 'A':(Zb,sp.Integer(0)), 'b':(X,W), 'B':(X,-W)}
inv = {'a':'A','A':'a','b':'B','B':'b'}
def h(word):
    q = (sp.Integer(1), sp.Integer(0))
    for ch in word: q = cmul(q, GEN[ch])
    return q
def inS(w):
    return ''.join(('A' if c=='a' else 'a' if c=='A' else c) for c in reversed(w)) == w
def reduced(w): return all(inv[w[i]] != w[i+1] for i in range(len(w)-1))
def ibeta(w): return ''.join('B' if c=='b' else 'b' if c=='B' else c for c in w)
def ialpha(w): return ''.join('A' if c=='a' else 'a' if c=='A' else c for c in w)

def word_latex(w):
    sym = {'a':r'\alpha','A':r'\alpha^{-1}','b':r'\beta','B':r'\beta^{-1}'}
    out=[]; i=0
    while i < len(w):
        j=i
        while j < len(w) and w[j]==w[i]: j+=1
        r=j-i; c=w[i]
        if r==1: out.append(sym[c])
        else:
            e = r if c in 'ab' else -r
            out.append({'a':r'\alpha','A':r'\alpha','b':r'\beta','B':r'\beta'}[c] + '^{%d}'%e)
        i=j
    return ''.join(out)

rows = defaultdict(list); seen = set()
for L in range(1, 8):
    for tup in itertools.product('aAbB', repeat=L):
        w=''.join(tup)
        if not (inS(w) and reduced(w)): continue
        na = sum(1 for c in w if c in 'aA'); nb = L-na
        if na % 2: continue
        m = na//2; n = nb
        orbit = {w, ibeta(w), ialpha(w), ialpha(ibeta(w))}
        if seen & orbit: continue
        # representative: middle letter 'b', then fewest capitals, then lex
        cands = [v for v in orbit if v[(L-1)//2]=='b']
        rep = sorted(cands, key=lambda v:(sum(1 for c in v if c in 'AB'), v))[0]
        seen.add(rep); seen |= orbit
        z1, z2 = h(rep)
        assert sp.expand(z1 - conj(z1)) == 0, rep
        lhs = sp.expand((Z*Zb)**(2*m) * (X**2 + W*Wb)**n)
        assert sp.expand(lhs - (z1**2 + z2*conj(z2))) == 0, rep
        norb = len(orbit)  # 2 iff m==0 (ialpha trivial), else 4
        rows[(m,n)].append((rep, sp.factor(z1), sp.factor(z2), norb))

out=[]
def emit_type(m, n, lst, note=""):
    out.append(r"\par\medskip\noindent\textbf{Type $(m,n)=(%d,%d)$}\quad %s"%(m,n,note))
    out.append(r"\par\nopagebreak\smallskip\noindent")
    out.append(r"{\small\begin{tabular}{@{}lll@{}}")
    out.append(r"\hline")
    out.append(r"$\sigma$ & $f_1$ & $F$ \\")
    out.append(r"\hline")
    for (wd, f1, F, norb) in lst:
        out.append(r"$%s$ & $%s$ & $%s$ \\[2pt]" % (word_latex(wd), sp.latex(f1), sp.latex(F)))
    out.append(r"\hline")
    out.append(r"\end{tabular}}")
    out.append("")

for (m,n) in sorted(k for k in rows if k[0]>=1 and 2*k[0]+k[1] <= 6):
    lst = sorted(rows[(m,n)], key=lambda r:(r[0].count('B'), r[0]))
    tot = sum(r[3]//2 for r in lst)  # classes = orbits * 2 (each 4-orbit = 2 classes)
    emit_type(m,n,lst, "(all $%d$ classes: the $%d$ rows below and their mirrors)"%(tot,len(lst)))
# showpieces from (2,3), length 7
lst = sorted(rows[(2,3)], key=lambda r:(r[0].count('B'), r[0]))[:3]
emit_type(2,3,lst, "($14$ classes in all; $3$ sample rows)")

with open('appendix_rows.tex','w') as f: f.write('\n'.join(out))
print({k: (len(v), sum(r[3]//2 for r in v)) for k,v in sorted(rows.items()) if k[0]>=1})
print("ALL VERIFIED")
