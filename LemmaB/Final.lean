import LemmaB.Main
import LemmaB.Small

/-!
# Lema B: enunciado final

La única hipótesis es el Lema B para `3 ∤ b` (transferencia 3-ádica clásica + Baker / Linek–Jiang;
JD-Jones-ASES/gn-lean). Los casos chicos están chequeados por certificados (`Small.lean`).
-/

namespace LemaB

theorem lemmaB_of_not_dvd
    (H3 : ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → 1 ≤ b → b ≤ m → b % 3 ≠ 0 → LemmaB m b) :
    ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → 1 ≤ b → b ≤ m → LemmaB m b :=
  lemmaB_all H3 lemmaB_small cB_55_54

end LemaB
