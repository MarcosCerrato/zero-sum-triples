"""Genera LemmaB/Small.lean: certificados del Lema B para 10 ≤ m < 46 (todo b) y (55, 54)."""
import sys
sys.path.insert(0, '.')
from verify import search_B, check_B
MS = list(range(10, 46, 3))
def L(T): return "[" + ", ".join("[" + ", ".join(str(x) for x in t) + "]" for t in T) + "]"
out = ["import LemmaB.Cert", "", "/-! Casos chicos del Lema B por certificados (generado por `lemaB/gen_certs.py`). -/", "",
       "namespace LemaB", ""]
def cert(m, b):
    T = search_B(m, b); check_B(m, b, T)
    T = sorted(T, key=lambda t: sorted(t) != sorted([-b, 0, b]))  # la central primero
    return f"theorem cB_{m}_{b} : LemmaB {m} {b} := lemmaB_of_check (L := {L(T)}) (by decide)\n"
for m in MS:
    for b in range(1, m + 1):
        out.append(cert(m, b))
    out.append(f"theorem cB_{m} : ∀ b, 1 ≤ b → b ≤ {m} → LemmaB {m} b := by\n  intro b h1 h2; interval_cases b\n  exacts [" +
               ", ".join(f"cB_{m}_{b}" for b in range(1, m + 1)) + "]\n")
out.append(cert(55, 54))
out.append("""theorem lemmaB_small : ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → m < 46 → 1 ≤ b → b ≤ m → LemmaB m b := by
  intro m b h1 h2 h3 h4 h5
  rcases (show """ + " ∨ ".join(f"m = {m}" for m in MS) + """ by omega) with """ + " | ".join("rfl" for _ in MS) + """
  exacts [""" + ", ".join(f"cB_{m} b h4 h5" for m in MS) + """]

end LemaB
""")
open('../LemmaB/Small.lean', 'w').write("\n".join(out))
print("ok")
