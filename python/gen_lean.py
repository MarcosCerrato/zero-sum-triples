"""Genera LemmaB/Families.lean a partir de families.py.
Cada familia se reparametriza con u = 2w+ρ (o u = w si vale para toda paridad), así todo es afín entero en w."""
import sys
from families import FAMILIES
R_OF = {2: 1, 0: 2, 1: 3}; N_OF = {2: 2, 0: 3, 1: 4}

def affine(f, w0):
    v = [f(w0 + t) for t in range(4)]
    a = v[1] - v[0]; b = v[0] - a * w0
    assert all(v[t] == a * (w0 + t) + b for t in range(4)), (v,)
    return a, b

def zexpr(a, b):
    w = "(w:ℤ)"
    if a == 0: return f"({b})"
    s = f"{a}*{w}" if a != 1 else w
    return f"({s}{'+' if b >= 0 else '-'}{abs(b)})" if b else f"({s})"

def nexpr(a, b):
    assert a >= 0 and (a > 0 or b >= 0)
    if a == 0: return f"{b}"
    if b < 0: return f"({a}*w-{-b})"
    return f"({a}*w+{b})" if b else f"({a}*w)"

def gen(name, F, delta, par, u0, kind, offs):
    step, rho = (1, 0) if par is None else (2, par)
    w0 = max(0, -(-(u0 - rho) // step))
    U = lambda w: step * w + rho
    X = lambda w: F(U(w))
    k = affine(lambda w: X(w)['k'], w0)
    keys = lambda w: list(X(w)['sig'].keys())
    vals = lambda w: list(X(w)['sig'].values())
    m = len(keys(w0))
    A = [affine(lambda w, i=i: keys(w)[i], w0) for i in range(m)]
    B = [affine(lambda w, i=i: vals(w)[i], w0) for i in range(m)]
    runs = []
    for side in ('X1', 'X2'):
        R = X(w0)[side][1]
        rs = []
        for q in range(len(R)):
            rs.append(tuple(affine(lambda w, q=q, c=c: X(w)[side][1][q][c], w0) for c in range(3)))
        runs.append(rs)
    K = nexpr(*k)
    if kind == 'main':
        j = (k[0], k[1] - R_OF[delta])
        E = f"Icc (-(({K} : ℕ) : ℤ)) (({K} : ℕ) : ℤ) \\ Icc (-(({nexpr(*j)} : ℕ) : ℤ)) (({nexpr(*j)} : ℕ) : ℤ)"
    else:
        o = kind[1]; n = (k[0], k[1] - N_OF[delta]); c = (k[0], k[1] - o)
        E = (f"Icc (-(({K} : ℕ) : ℤ)) (({K} : ℕ) : ℤ) \\ (Icc (-(({nexpr(*n)} : ℕ) : ℤ)) (({nexpr(*n)} : ℕ) : ℤ) ∪ "
             f"{{-(({nexpr(*c)} : ℕ) : ℤ), (({nexpr(*c)} : ℕ) : ℤ)}})")
    vec = lambda L: "![" + ", ".join(zexpr(*x) for x in L) + "]"
    rvec = lambda rs: "![" + ", ".join(f"⟨{zexpr(*x)}, {zexpr(*y)}, {zexpr(*l)}⟩" for x, y, l in rs) + "]"
    inj = "intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega"
    memK = "intro i; fin_cases i <;> simp <;> omega"
    side = lambda: f"""apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by {inj}) (by {memK})]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega"""
    return f"""
/-- Familia `{name}` (ver `lemaB/families.py`): `u = {step}w+{rho}`, `w ≥ {w0}`. -/
noncomputable def xsys_{name} (w : ℕ) (hw : {w0} ≤ w) :
    XSys {K} ({E}) := by
  refine xsysOf {K} {vec(A)} {vec(B)} _ ?_ ?_ ?_ ?_ ?_ ?_
    {rvec(runs[0])}
    {rvec(runs[1])} ?_ ?_
  · {inj}
  · {inj}
  · {inj}
  · ext z; simp [Fin.exists_fin_succ]; omega
  · {memK}
  · {memK}
  · {side()}
  · {side()}
""", (name, delta, step, rho, w0, kind)

if __name__ == "__main__":
    names = sys.argv[1:] or list(FAMILIES)
    out = ["import LemmaB.Builder", "", "/-! Familias explícitas de sistemas X (generado por `lemaB/gen_lean.py`). -/", "",
           "namespace LemaB", "open Finset GN", "", "set_option maxHeartbeats 4000000", ""]
    meta = []
    for nm in names:
        txt, mt = gen(nm, *FAMILIES[nm]); out.append(txt); meta.append(mt)
    out.append("end LemaB\n")
    open('../LemmaB/Families.lean', 'w').write("\n".join(out))
    print(meta)
