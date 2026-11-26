"""Familias explícitas de "sistemas X" para el Lema B con b ≡ 0 (mod 3). Ver PROOF.md.

Un sistema X para (k, D) es: σ: A → B biyección con desplazamientos σ(x)−x = ±D (cada uno una vez) y
particiones de X1 = [−k..k]∖A y X2 = [−k..k]∖B en ternas de suma −1.
Cada X_i se da como (iota, runs): I = [iota..iota+t−1] y "corridas" (x0, y0, L) = pares (x0+i, y0+i), i < L,
completados a la terna (x0+i, y0+i, −1−x0−y0−2i); el tercer elemento recorre I exactamente una vez.
Notación: m = 3k+1, b = 3c, u = ⌊k/3⌋.
"""
# Explicit X-system families. Each returns dict: k, D (list of displacements d>0), sig {x: sigma(x)},
# X1, X2 each given as (iota, runs) meaning: I=[iota..iota+t-1], J-pairs runs (x0,y0,L): pairs (x0+i,y0+i),
# triples (x0+i, y0+i, -1-(x0+y0+2i)) -- the third element must sweep I exactly.
def F2(u):  # k = 3u+2, D = {k}
    k=3*u+2
    return dict(k=k, D=[k], sig={-u-1:2*u+1, k:0},
                X1=(-k,[(-u,2*u+1,u+1),(1,u+1,u)]),
                X2=(-k,[(-u-1,2*u+2,u+1),(1,u+1,u)]))
def F0e(u):  # k = 3u, u even, D={k-1,k}
    w=u//2; k=3*u
    R=[(-2*w,6*w,1),(-2*w+2,4*w+1,2*w-1),(1,2*w+1,w-1),(w,w+1,1),(w+2,3*w,w-1)]
    return dict(k=k, D=[k-1,k], sig={-2*w-1:4*w-1, 4*w-1:-2*w-1, -2*w+1:4*w, 4*w:-2*w+1},
                X1=(-k,R), X2=(-k,R))
def F0o(u):  # k = 3u, u odd, D={k-1,k}
    k=3*u
    R=[(-u,2*u+2,1),(-u+2,2*u+3,u-2),(0,2*u-1,2),(2,u+2,(u-5)//2),((u-1)//2,(u+3)//2,2),((u+7)//2,(3*u-1)//2,(u-3)//2)]
    return dict(k=k, D=[k-1,k], sig={-u-1:2*u-2, 2*u-2:-u-1, -u+1:2*u+1, 2*u+1:-u+1}, X1=(-k,R), X2=(-k,R))
def check(F):
    k=F['k']; D=F['D']; sig=F['sig']; r=len(D)
    assert (2*k+1-2*r)%3==0; t=(2*k+1-2*r)//3
    A=sorted(sig); B=sorted(sig.values())
    disp=sorted(sig[x]-x for x in sig)
    assert disp==sorted(D+[-d for d in D]), 'disp'
    assert all(-k<=x<=k for x in A+B)
    tri=[]
    for (iota,R),H in ((F['X1'],A),(F['X2'],B)):
        T=[]
        for x0,y0,L in R:
            assert L>=0
            for i in range(L): T.append((x0+i,y0+i,-1-(x0+y0+2*i)))
        flat=sorted(v for T_ in T for v in T_)
        assert flat==sorted(x for x in range(-k,k+1) if x not in H), 'cover'
        assert sorted(T_[2] for T_ in T)==list(range(iota,iota+t)), 'I'
        tri.append(T)
    return t,tri
def F1o(u):  # k = 3u+1, u odd, D={k-2,k-1,k}; A = {-k,-k+1,-u,k-2,k-1,k} -> B = {-2..2, 2u-1}
    k=3*u+1
    sig={-k:-1, -k+1:1, -u:2*u-1, k-2:-2, k-1:0, k:2}
    X1=(-k+2,[(-u+1,2*u-1,u),(1,u,u-1)])
    X2=(-k,[(-u-2,2*u+4,u-2),(-4,2*u+2,2),(3,u,(u-5)//2),((u+1)//2,(3*u+3)//2,(u-5)//2),(u-2,2*u,2),((3*u-5)//2,(3*u-1)//2,2)])
    return dict(k=k,D=[k-2,k-1,k],sig=sig,X1=X1,X2=X2)
def _F1o_X2(u):
    k=3*u+1
    return (-k,[(-u-2,2*u+4,u-2),(-4,2*u+2,2),(3,u,(u-5)//2),((u+1)//2,(3*u+3)//2,(u-5)//2),(u-2,2*u,2),((3*u-5)//2,(3*u-1)//2,2)])
def F1o_top_km1(u):  # k=3u+1, u odd, c=k-1: D={k-3,k-2,k}
    k=3*u+1
    sig={-k:0, -k+1:-2, -u:2*u-1, k-2:1, k-1:-1, k:2}
    return dict(k=k,D=[k-3,k-2,k],sig=sig,X1=(-k+2,[(-u+1,2*u-1,u),(1,u,u-1)]),X2=_F1o_X2(u))
def F1o_top_k(u):  # k=3u+1, u odd, c=k: D={k-3,k-2,k-1}
    k=3*u+1
    sig={-k:-1, -k+1:-2, -u:2*u-1, k-2:1, k-1:0, k:2}
    return dict(k=k,D=[k-3,k-2,k-1],sig=sig,X1=(-k+2,[(-u+1,2*u-1,u),(1,u,u-1)]),X2=_F1o_X2(u))
def F1e_top_km2(u):  # k=3u+1, u even, c=k-2: D={k-3,k-1,k}; B={-3,-2,0,1,2,2u+1}
    k=3*u+1
    sig={-k:-3, -k+1:0, -u:2*u+1, k-2:-2, k-1:2, k:1}
    X2=(-k,[(-u-2,2*u+4,u-2),(-4,2*u+3,1),(-1,2*u+2,1),(3,u,(u-4)//2),(u//2+1,(3*u+4)//2,u//2-1),((3*u-4)//2,3*u//2,2)])
    return dict(k=k,D=[k-3,k-1,k],sig=sig,X1=(-k+2,[(-u+1,2*u-1,u),(1,u,u-1)]),X2=X2)
def psl(k,t,e0,e1):
    v=(t-1)//2; iota=-k+e0; p=iota+t+e1
    return (iota,[(p,p+3*v+1,v+1),(p+v+1,p+2*v+1,v)])
def F0e_top_km1(u):  # k=3u, u even, c=k-1: D={k-2,k}; A={-k,-u,k-1,k} -> B={-2,0,1,2u}
    k=3*u; t=2*u-1
    sig={-k:-2, -u:2*u, k-1:1, k:0}
    X2=(-k,[(-u-1,2*u+2,u-1),(-1,2*u+1,1),(2,u,u//2-1),(u//2+1,(3*u+2)//2,u//2-1),((3*u-2)//2,3*u//2,1)])
    return dict(k=k,D=[k-2,k],sig=sig,X1=psl(k,t,1,1),X2=X2)
def F2o_top_k(u):  # k=3u+2, u odd, c=k: D={k-1}; A={-u-1,k} -> B={1,2u}
    k=3*u+2
    X2=(-k,[(-u-1,2*u+2,u+1),(0,u+2,1),(2,2*u+1,1),(3,u+3,(u-3)//2),((u+3)//2,(u+5)//2,1),((u+7)//2,(3*u+3)//2,(u-3)//2)])
    return dict(k=k,D=[k-1],sig={-u-1:2*u, k:1},X1=(-k,[(-u,2*u+1,u+1),(1,u+1,u)]),X2=X2)
def F0o_top_k(u):  # k=3u, u odd, c=k: D={k-2,k-1}; involution A={-u-1,2u-2,-u+2,2u}
    k=3*u
    sig={-u-1:2*u-2, 2*u-2:-u-1, -u+2:2*u, 2*u:-u+2}
    R=[(-u,3*u-1,2),(-u+3,2*u-1,1),(-u+4,2*u+1,u-2),(2,u+2,(u-5)//2),((u-1)//2,(u+3)//2,2),((u+7)//2,(3*u-1)//2,(u-3)//2)]
    return dict(k=k,D=[k-2,k-1],sig=sig,X1=(-k,R),X2=(-k,R))
def F2e_top_k(u):  # k=3u+2, u even, c=k: D={k-1}; involution {-u/2, 5u/2+1}
    k=3*u+2; h=u//2
    sig={-h:5*h+1, 5*h+1:-h}
    R=[(-u-1,3*u+1,2),(-u+1,2*u+1,h-1),(-h+1,5*h+2,h-1),(0,u+1,h+1),(h+1,5*h,1),(h+2,3*h+2,h-1)]
    return dict(k=k,D=[k-1],sig=sig,X1=(-k,R),X2=(-k,R))
def F1o_top_km2(u):  # k=3u+1, u odd, c=k-2: D={k-3,k-1,k}; A={-k,-k+1,-u+1,k-3,k-1,k} -> Bo
    k=3*u+1
    sig={-k:-1, -k+1:1, -u+1:2*u-1, k-3:-2, k-1:2, k:0}
    X1=(-k+2,[(-u,3*u-1,1),(-u+2,2*u-2,(u-1)//2),(-(u-3)//2,(5*u-3)//2,(u-1)//2),(1,u,(u-1)//2),((u+1)//2,(5*u-5)//2,1),((u+3)//2,(3*u-1)//2,(u-3)//2)])
    return dict(k=k,D=[k-3,k-1,k],sig=sig,X1=X1,X2=_F1o_X2(u))
def F0e_top_k(u):  # k=3u, u even, c=k: D={k-2,k-1}; involution {-u-1,2u-3},{-u+2,2u+1}
    k=3*u; h=u//2
    sig={-u-1:2*u-3, 2*u-3:-u-1, -u+2:2*u+1, 2*u+1:-u+2}
    R=[(-u,2*u+2,2),(-u+3,2*u+4,u-3),(0,2*u-2,3),(3,u+3,h-4),(h-1,h+2,3),(h+5,3*h-1,h-2)]
    return dict(k=k,D=[k-2,k-1],sig=sig,X1=(-k,R),X2=(-k,R))
def _F1e_X2(u):  # complement of Be={-3,-2,0,1,2,2u+1}, u even
    k=3*u+1
    return (-k,[(-u-2,2*u+4,u-2),(-4,2*u+3,1),(-1,2*u+2,1),(3,u,(u-4)//2),(u//2+1,(3*u+4)//2,u//2-1),((3*u-4)//2,3*u//2,2)])
def F1e(u):  # k=3u+1, u even, main D={k-2,k-1,k}; A={-k,-k+1,-u+1,k-3,k-1,k} -> Be
    k=3*u+1; h=u//2
    sig={k-3:-3, -k:-2, k-1:0, -k+1:1, k:2, -u+1:2*u+1}
    X1=(-k+2,[(-u,3*u-1,1),(-u+2,2*u-2,u),(2,u-1,h-1),(h+1,3*h,h-2),(3*h-2,3*h-1,1)])
    return dict(k=k,D=[k-2,k-1,k],sig=sig,X1=X1,X2=_F1e_X2(u))
def _F1e_topX1(u):
    k=3*u+1; h=u//2
    return (-k+2,[(-u,3*u-2,2),(-u+3,2*u-2,u-1),(2,u-2,h-1),(h+1,3*h+1,h-3),(3*h-3,3*h-1,2)])
def F1e_top_km1(u):  # c=k-1: D={k-3,k-2,k}; A={-k,-k+1,-u+2,k-4,k-1,k}
    k=3*u+1
    sig={-k:-3, k-4:-2, k:0, -k+1:1, k-1:2, -u+2:2*u+1}
    return dict(k=k,D=[k-3,k-2,k],sig=sig,X1=_F1e_topX1(u),X2=_F1e_X2(u))
def F1e_top_k(u):  # c=k: D={k-3,k-2,k-1}
    k=3*u+1
    sig={-k:-3, k-4:-2, -k+1:0, k:1, k-1:2, -u+2:2*u+1}
    return dict(k=k,D=[k-3,k-2,k-1],sig=sig,X1=_F1e_topX1(u),X2=_F1e_X2(u))


def F0o_top_km1(u):  # k=3u, u odd, c=k-1: D={k-2,k}; A={-2,0,1,2u} -> B={-k,-u,k-1,k} (PSL)
    k=3*u; t=2*u-1
    sig={-2:-k, 2*u:-u, 1:k-1, 0:k}
    X1=(-k,[(-u-1,2*u+2,u-1),(-1,2*u-2,1),(2,u,(u-5)//2),((u-1)//2,(3*u-1)//2,(u-3)//2),(u-2,2*u+1,1),(u-1,2*u-1,1),((3*u-5)//2,(3*u-3)//2,1)])
    return dict(k=k,D=[k-2,k],sig=sig,X1=X1,X2=psl(k,t,1,1))


# nombre: (función, k mod 3, paridad de u (None = cualquiera), u mínimo, tipo, offsets de D respecto de k)
#   tipo 'main': T = [1..k−r] (adentro Lema B(k−r, c)), sirve para c ≤ k−r.
#   tipo ('top', o): c = k−o, T = [1..n] ∪ {c} (adentro {−c,0,c} + Lema 1 en ±[1..n]).
FAMILIES = {
    'F2':          (F2,          2, None, 1, 'main',       [0]),
    'F2o_top_k':   (F2o_top_k,   2, 1,    3, ('top', 0),   [1]),
    'F2e_top_k':   (F2e_top_k,   2, 0,    2, ('top', 0),   [1]),
    'F0e':         (F0e,         0, 0,    2, 'main',       [1, 0]),
    'F0o':         (F0o,         0, 1,    5, 'main',       [1, 0]),
    'F0e_top_km1': (F0e_top_km1, 0, 0,    2, ('top', 1),   [2, 0]),
    'F0o_top_km1': (F0o_top_km1, 0, 1,    5, ('top', 1),   [2, 0]),
    'F0e_top_k':   (F0e_top_k,   0, 0,    8, ('top', 0),   [2, 1]),
    'F0o_top_k':   (F0o_top_k,   0, 1,    5, ('top', 0),   [2, 1]),
    'F1e':         (F1e,         1, 0,    4, 'main',       [2, 1, 0]),
    'F1o':         (F1o,         1, 1,    5, 'main',       [2, 1, 0]),
    'F1e_top_km2': (F1e_top_km2, 1, 0,    4, ('top', 2),   [3, 1, 0]),
    'F1e_top_km1': (F1e_top_km1, 1, 0,    6, ('top', 1),   [3, 2, 0]),
    'F1e_top_k':   (F1e_top_k,   1, 0,    6, ('top', 0),   [3, 2, 1]),
    'F1o_top_km2': (F1o_top_km2, 1, 1,    5, ('top', 2),   [3, 1, 0]),
    'F1o_top_km1': (F1o_top_km1, 1, 1,    5, ('top', 1),   [3, 2, 0]),
    'F1o_top_k':   (F1o_top_k,   1, 1,    5, ('top', 0),   [3, 2, 1]),
}
R_OF = {2: 1, 0: 2, 1: 3}          # r = |D| en el caso principal
N_OF = {2: 2, 0: 3, 1: 4}          # en el caso tope, n = k − N_OF


def check_family(F):
    t, tri = check(F)
    return t, tri


def family_for(k, c):
    """Devuelve (sistema X, tipo, parámetro interno): j para 'main', n para 'top'."""
    d, u = k % 3, k // 3
    if c <= k - R_OF[d]:
        kind, inner = 'main', k - R_OF[d]
    else:
        kind, inner = ('top', k - c), k - N_OF[d]
    for name, (F, dd, par, u0, kk, offs) in FAMILIES.items():
        if dd == d and kk == kind and (par is None or u % 2 == par) and u >= u0:
            X = F(u)
            assert sorted(X['D']) == sorted(k - o for o in offs)
            return X, ('main' if kind == 'main' else 'top'), inner
    raise KeyError(f'sin familia para k={k}, c={c} (u={u}, tipo={kind})')
