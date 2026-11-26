import LemmaB.Families

/-!
# Lema B: teorema principal (PROOF.md §6)

Suponiendo
* `H3`: el Lema B para `3 ∤ b` (transferencia 3-ádica clásica + Baker / Linek–Jiang; JD-Jones-ASES/gn-lean),
* `Hsmall`: el Lema B para `10 ≤ m < 46` (verificación por computadora),
* `H55`: el caso `(m, b) = (55, 54)` (verificación por computadora),

el Lema B vale para todo `m ≡ 1 (mod 3)`, `m ≥ 10` y todo `b ∈ [1..m]`.
-/

namespace LemaB

theorem lemmaB_all
    (H3 : ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → 1 ≤ b → b ≤ m → b % 3 ≠ 0 → LemmaB m b)
    (Hsmall : ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → m < 46 → 1 ≤ b → b ≤ m → LemmaB m b)
    (H55 : LemmaB 55 54) :
    ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → 1 ≤ b → b ≤ m → LemmaB m b := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro b hm h10 hb1 hbm
  by_cases h3 : b % 3 ≠ 0
  · exact H3 m b hm h10 hb1 hbm h3
  by_cases hs : m < 46
  · exact Hsmall m b hm h10 hs hb1 hbm
  by_cases h55 : m = 55 ∧ b = 54
  · obtain ⟨rfl, rfl⟩ := h55; exact H55
  have IH' : ∀ j c : ℕ, j < m → j % 3 = 1 → 10 ≤ j → 1 ≤ c → c ≤ j → LemmaB j c :=
    fun j c hj a1 a2 a3 a4 => IH j hj c a1 a2 a3 a4
  set k := m / 3 with hk
  set c := b / 3 with hc
  have hmk : m = 3 * k + 1 := by omega
  have hbc : b = 3 * c := by omega
  have hk15 : 15 ≤ k := by omega
  have hc1 : 1 ≤ c := by omega
  have hck : c ≤ k := by omega
  -- k ≡ 2 (mod 3): caso principal con F2 (j = k − 1); tope c = k según la paridad de u
  rcases (show k % 3 = 2 ∨ k % 6 = 0 ∨ k % 6 = 3 ∨ k % 6 = 1 ∨ k % 6 = 4 by omega) with
    hr | hr | hr | hr | hr
  · by_cases hcj : c ≤ 3 * (k / 3) + 1
    · have := lemmaB_main (3 * (k / 3) + 2) (3 * (k / 3) + 1) c (by omega)
        (IH' _ c (by omega) (by omega) (by omega) hc1 hcj) (xsys_F2 (k / 3) (by omega))
      convert this using 2 <;> omega
    · rcases (show k % 6 = 2 ∨ k % 6 = 5 by omega) with hp | hp
      · have := lemmaB_top (6 * (k / 6) + 2) (6 * (k / 6)) (6 * (k / 6) + 2) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F2e_top_k (k / 6) (by omega))
        convert this using 2 <;> omega
      · have := lemmaB_top (6 * (k / 6) + 5) (6 * (k / 6) + 3) (6 * (k / 6) + 5) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F2o_top_k (k / 6) (by omega))
        convert this using 2 <;> omega
  -- k ≡ 0 (mod 6)
  · by_cases hcj : c ≤ 6 * (k / 6) - 2
    · have := lemmaB_main (6 * (k / 6)) (6 * (k / 6) - 2) c (by omega)
        (IH' _ c (by omega) (by omega) (by omega) hc1 hcj) (xsys_F0e (k / 6) (by omega))
      convert this using 2 <;> omega
    · rcases (show c = 6 * (k / 6) - 1 ∨ c = 6 * (k / 6) by omega) with hc' | hc'
      · have := lemmaB_top (6 * (k / 6)) (6 * (k / 6) - 3) (6 * (k / 6) - 1) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F0e_top_km1 (k / 6) (by omega))
        convert this using 2 <;> omega
      · have h4 : 4 ≤ k / 6 := by
          by_contra h
          have : k = 18 := by omega
          exact h55 ⟨by omega, by omega⟩
        have := lemmaB_top (6 * (k / 6)) (6 * (k / 6) - 3) (6 * (k / 6)) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F0e_top_k (k / 6) h4)
        convert this using 2 <;> omega
  -- k ≡ 3 (mod 6)
  · by_cases hcj : c ≤ 6 * (k / 6) + 1
    · have := lemmaB_main (6 * (k / 6) + 3) (6 * (k / 6) + 1) c (by omega)
        (IH' _ c (by omega) (by omega) (by omega) hc1 hcj) (xsys_F0o (k / 6) (by omega))
      convert this using 2 <;> omega
    · rcases (show c = 6 * (k / 6) + 2 ∨ c = 6 * (k / 6) + 3 by omega) with hc' | hc'
      · have := lemmaB_top (6 * (k / 6) + 3) (6 * (k / 6)) (6 * (k / 6) + 2) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F0o_top_km1 (k / 6) (by omega))
        convert this using 2 <;> omega
      · have := lemmaB_top (6 * (k / 6) + 3) (6 * (k / 6)) (6 * (k / 6) + 3) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F0o_top_k (k / 6) (by omega))
        convert this using 2 <;> omega
  -- k ≡ 1 (mod 6)
  · by_cases hcj : c ≤ 6 * (k / 6) - 2
    · have := lemmaB_main (6 * (k / 6) + 1) (6 * (k / 6) - 2) c (by omega)
        (IH' _ c (by omega) (by omega) (by omega) hc1 hcj) (xsys_F1e (k / 6) (by omega))
      convert this using 2 <;> omega
    · rcases (show c = 6 * (k / 6) - 1 ∨ c = 6 * (k / 6) ∨ c = 6 * (k / 6) + 1 by omega) with
        hc' | hc' | hc'
      · have := lemmaB_top (6 * (k / 6) + 1) (6 * (k / 6) - 3) (6 * (k / 6) - 1) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F1e_top_km2 (k / 6) (by omega))
        convert this using 2 <;> omega
      · have := lemmaB_top (6 * (k / 6) + 1) (6 * (k / 6) - 3) (6 * (k / 6)) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F1e_top_km1 (k / 6) (by omega))
        convert this using 2 <;> omega
      · have := lemmaB_top (6 * (k / 6) + 1) (6 * (k / 6) - 3) (6 * (k / 6) + 1) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F1e_top_k (k / 6) (by omega))
        convert this using 2 <;> omega
  -- k ≡ 4 (mod 6)
  · by_cases hcj : c ≤ 6 * (k / 6) + 1
    · have := lemmaB_main (6 * (k / 6) + 4) (6 * (k / 6) + 1) c (by omega)
        (IH' _ c (by omega) (by omega) (by omega) hc1 hcj) (xsys_F1o (k / 6) (by omega))
      convert this using 2 <;> omega
    · rcases (show c = 6 * (k / 6) + 2 ∨ c = 6 * (k / 6) + 3 ∨ c = 6 * (k / 6) + 4 by omega) with
        hc' | hc' | hc'
      · have := lemmaB_top (6 * (k / 6) + 4) (6 * (k / 6)) (6 * (k / 6) + 2) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F1o_top_km2 (k / 6) (by omega))
        convert this using 2 <;> omega
      · have := lemmaB_top (6 * (k / 6) + 4) (6 * (k / 6)) (6 * (k / 6) + 3) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F1o_top_km1 (k / 6) (by omega))
        convert this using 2 <;> omega
      · have := lemmaB_top (6 * (k / 6) + 4) (6 * (k / 6)) (6 * (k / 6) + 4) (by omega) (by omega)
          (H3 _ _ (by omega) (by omega) (by omega) le_rfl (by omega))
          (xsys_F1o_top_k (k / 6) (by omega))
        convert this using 2 <;> omega

end LemaB
