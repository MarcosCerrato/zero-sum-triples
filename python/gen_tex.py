"""Genera paper/families.tex (tablas de las 17 familias, con u = 2w+ρ) desde families.py."""
from families import FAMILIES
from gen_lean import affine
R_OF = {2: 1, 0: 2, 1: 3}
def tx(a, b):
    if a == 0: return f"{b}"
    s = {1: "w", -1: "-w"}.get(a, f"{a}w")
    return s + (f"{'+' if b > 0 else '-'}{abs(b)}" if b else "")
def koff(o): return "k" if o == 0 else f"k-{o}"
out = []
for name, (F, delta, par, u0, kind, offs) in FAMILIES.items():
    step, rho = (1, 0) if par is None else (2, par)
    w0 = max(0, -(-(u0 - rho) // step))
    X = lambda w: F(step * w + rho)
    k = affine(lambda w: X(w)['k'], w0)
    m = len(X(w0)['sig'])
    A = [affine(lambda w, i=i: list(X(w)['sig'].keys())[i], w0) for i in range(m)]
    B = [affine(lambda w, i=i: list(X(w)['sig'].values())[i], w0) for i in range(m)]
    sides = []
    for sd in ('X1', 'X2'):
        R = X(w0)[sd][1]
        sides.append([tuple(affine(lambda w, q=q, c=c: X(w)[sd][1][q][c], w0) for c in range(3)) for q in range(len(R))])
    D = "\\{" + ",".join(koff(o) for o in sorted(offs, reverse=True)) + "\\}"
    case = "main case, $c\\le k-%d$" % R_OF[delta] if kind == 'main' else "top case, $c=%s$" % koff(kind[1])
    sig = ",\\ ".join(f"\\mbox{{${tx(*a)}\\mapsto {tx(*b)}$}}" for a, b in zip(A, B))
    runs = lambda rs: ",\\ ".join(f"\\mbox{{$({tx(*x)},\\,{tx(*y)},\\,{tx(*l)})$}}" for x, y, l in rs)
    same = sides[0] == sides[1]
    nm = name.replace('_', '\\_')
    out.append(f"""\\begin{{family}}{{{nm}}}{{$k={tx(*k)}$, $w\\ge {w0}$; {case}; $D={D}$}}
\\famrow{{$\\sigma$}}{{{sig}}}
\\famrow{{$X_1$}}{{{runs(sides[0])}}}
\\famrow{{$X_2$}}{{{'same as $X_1$' if same else runs(sides[1])}}}
\\end{{family}}
""")
import os
HERE = os.path.dirname(os.path.abspath(__file__))
open(os.path.join(HERE, '..', 'paper', 'families.tex'), 'w').write("\n".join(out))
print(len(out), "familias")
