"""Verificador reproducible: Lema B para b ≡ 0 (mod 3) vía la "transferencia 3-ádica con bloque (0,0,0)".

Lema B(m, b): para m ≡ 1 (mod 3), partir ±([1..m]∖{b}) en ternas de suma 0
(equivalente: [−m..m] en ternas de suma 0 con {−b, 0, b} como una de ellas).

Uso:
    python3 verify.py families [UMAX]   # chequea todas las familias explícitas para u ≤ UMAX (default 400)
    python3 verify.py build M           # construye y chequea Lema B(m, b) para todo m ≤ M, b ≡ 0 (mod 3)

La construcción (ver PROOF.md):
  m = 3k+1, b = 3c. Elegimos T ⊂ [1..k] con c ∈ T y un "sistema X" para D = [1..k]∖T:
    σ: A → B biyección con desplazamientos σ(x)−x = ±D (cada uno una vez),
    X1 = [−k..k]∖A y X2 = [−k..k]∖B partidos en ternas de suma −1.
  Ternas finales:
    3·(ternas de suma 0 de {0} ∪ ±T con {−c,0,c})      (residuo 0)
    {3x+1 : x ∈ τ}  para cada terna τ de X1             (residuo 1)
    {−3y−1 : y ∈ τ} para cada terna τ de X2             (residuo 2)
    (3(σ(x)−x), 3x+1, −3σ(x)−1) para x ∈ A              (mixtas)
  Caso principal: T = [1..j], j = k−r ≡ 1 (mod 3), c ≤ j  → adentro va Lema B(j, c) (recursión).
  Caso tope:      T = [1..n] ∪ {c}, n ≡ 0 (mod 3), c > j  → adentro va {−c,0,c} + Lema B(n+1, n+1) (b = m: Lema 1 de GN).
Los casos 3 ∤ b (que aparecen adentro de la recursión) se arman con la transferencia 3-ádica clásica
(gurvich-naumova/fable_review/pipeline.py; las secuencias de Skolem/Langford se buscan por computadora en lugar de
citar a Baker / Linek–Jiang). Los m chicos (base) se resuelven por búsqueda exacta.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from families import check_family, family_for
from xc import solve_restarts, zs

M_BASE = 46   # m < M_BASE: búsqueda exacta
MISSING = []  # casos sin familia explícita (resueltos por búsqueda)


def search_B(m, b):
    Y = [x for x in range(1, m + 1) if x != b]
    it, op = zs(Y)
    s = solve_restarts(it, op, tries=400, per=20000, seed=m * 1000 + b)
    return [tuple(op[n]) for n in s] + [(-b, 0, b)]


def lemma1(n):
    """ternas de suma 0 que parten ±[1..n], n ≡ 0 (mod 3) (= Lema B(n+1, n+1) sin la terna {−b,0,b})."""
    if n == 0:
        return []
    T = lemmaB(n + 1, n + 1)
    return [t for t in T if 0 not in t]


def lemmaB(m, b):
    """Devuelve ternas de suma 0 que parten [−m..m], incluida (−b, 0, b)."""
    assert m % 3 == 1 and 1 <= b <= m
    if m < M_BASE:
        return search_B(m, b)
    if b % 3:
        import pipeline
        k = (m - 1) // 3
        tr, how = pipeline.lemmaB(k, b)
        assert tr is not None, (m, b, how)
        return [tuple(t) for t in tr] + [(-b, 0, b)]
    k, c = (m - 1) // 3, b // 3
    try:
        F, kind, inner = family_for(k, c)
    except KeyError:
        MISSING.append((m, b))
        return search_B(m, b)
    if kind == 'main':
        j = inner
        inner_tr = lemmaB(j, c)                               # incluye (−c, 0, c)
    else:
        n = inner
        inner_tr = lemma1(n) + [(-c, 0, c)]
    t, (T1, T2) = check_family(F)
    sig = F['sig']
    out = [tuple(3 * x for x in tr) for tr in inner_tr]
    out += [tuple(3 * x + 1 for x in tr) for tr in T1]
    out += [tuple(-3 * y - 1 for y in tr) for tr in T2]
    out += [(3 * (sig[x] - x), 3 * x + 1, -3 * sig[x] - 1) for x in sig]
    return out


def check_B(m, b, T):
    assert all(len(t) == 3 and sum(t) == 0 for t in T), 'suma'
    assert sorted(v for t in T for v in t) == list(range(-m, m + 1)), 'cobertura'
    assert any(sorted(t) == [-b, 0, b] for t in T), 'terna {−b,0,b}'


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'families'
    if cmd == 'families':
        from families import FAMILIES
        UMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 400
        for name, (F, delta, par, u0, kind, Doffs) in FAMILIES.items():
            us = [u for u in range(u0, UMAX + 1) if par is None or u % 2 == par]
            for u in us:
                check_family(F(u))
            print(f'{name:16s} ok para u = {us[0]}..{us[-1]} ({len(us)} valores)')
    elif cmd == 'symbolic':
        # Cada familia es afín en u dentro de cada clase u ≡ ρ (mod 4). La validez de un sistema X es una
        # combinación booleana de comparaciones f(u) ≤ g(u) + s (s ∈ {−2..2}) entre los extremos afines
        # (corridas, I, huecos, ±k) y de paridades, que son constantes en cada clase mód 4. Cada comparación es
        # constante a partir de su punto de cruce; arriba del máximo cruce U* el resultado no cambia.
        # Acá calculamos U* y chequeamos todos los u ≤ UMAX; si UMAX > U* + 8, vale para todo u ≥ u0.
        from families import FAMILIES
        from fractions import Fraction as Fr
        UMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 400
        def quantities(X):
            k = X['k']; t = (2 * k + 1 - 2 * len(X['D'])) // 3; q = [k, -k, t]
            for a, b in sorted(X['sig'].items()): q += [a, b]
            for iota, R in (X['X1'], X['X2']):
                q += [iota, iota + t - 1]
                for x0, y0, L in R:
                    q += [x0, y0, L, x0 + L - 1, y0 + L - 1, -1 - x0 - y0, -1 - x0 - y0 - 2 * (L - 1)]
            return q
        worst = 0
        for name, (F, delta, par, u0, kind, Doffs) in FAMILIES.items():
            for rho in range(4):
                us = [u for u in range(u0, u0 + 40) if u % 4 == rho and (par is None or u % 2 == par)]
                if len(us) < 3: continue
                q0, q1, q2 = (quantities(F(u)) for u in us[:3])
                assert len(q0) == len(q1) == len(q2)
                lin = [(Fr(b - a, 4), Fr(a) - Fr(b - a, 4) * us[0]) for a, b in zip(q0, q1)]
                assert all(sl * us[2] + c0 == v for (sl, c0), v in zip(lin, q2)), name
                U = us[0]
                for i in range(len(lin)):
                    for j in range(len(lin)):
                        ds = lin[i][0] - lin[j][0]
                        if ds == 0: continue
                        for sh in range(-2, 3):
                            U = max(U, (lin[j][1] + sh - lin[i][1]) / ds)
                worst = max(worst, U)
                for u in range(us[0], UMAX + 1, 4):
                    check_family(F(u))
            print(f'{name:16s} afín en cada clase mód 4; chequeado u ≤ {UMAX}')
        print(f'máximo punto de cruce U* = {float(worst):.1f}  (< {UMAX}): las familias valen para todo u ≥ u0')
        assert worst + 8 < UMAX
    elif cmd == 'build':
        M = int(sys.argv[2])
        n = 0
        for m in range(M_BASE, M + 1, 3):
            for b in range(3, m + 1, 3):
                check_B(m, b, lemmaB(m, b)); n += 1
            print(f'm={m}: ok', flush=True)
        print('sin familia explícita (búsqueda):', sorted(set(MISSING)))
        print(f'OK: {n} instancias con b ≡ 0 (mod 3), {M_BASE} ≤ m ≤ {M}')
