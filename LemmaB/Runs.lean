import LemmaB.Transfer

/-!
# Corridas: particiones explícitas en ternas de suma −1

Una corrida `(x0, y0, L)` da las ternas `{x0+i, y0+i, −1−x0−y0−2i}` para `0 ≤ i < L` (PROOF.md §3).
`runs_isPart` reduce "estas ternas parten `X`" a tres condiciones aritméticas (pertenencia, inyectividad
y conteo), que en cada familia se descargan con `omega`.
-/

namespace LemaB

open Finset GN

/-- Una corrida. -/
structure Run where
  x0 : ℤ
  y0 : ℤ
  L : ℤ

/-- Elemento número `s` (0, 1 o 2) de la terna `i` de la corrida. -/
def Run.el (R : Run) (i : ℤ) : Fin 3 → ℤ
  | 0 => R.x0 + i
  | 1 => R.y0 + i
  | 2 => -1 - R.x0 - R.y0 - 2 * i

/-- La terna `i` de la corrida. -/
def Run.tri (R : Run) (i : ℤ) : Finset ℤ := {R.x0 + i, R.y0 + i, -1 - R.x0 - R.y0 - 2 * i}

lemma Run.tri_eq (R : Run) (i : ℤ) : R.tri i = {R.el i 0, R.el i 1, R.el i 2} := rfl

lemma Run.mem_tri {R : Run} {i z : ℤ} : z ∈ R.tri i ↔ ∃ s, R.el i s = z := by
  rw [Run.tri_eq]; simp only [mem_insert, mem_singleton]
  constructor
  · rintro (h | h | h) <;> exact ⟨_, h.symm⟩
  · rintro ⟨s, rfl⟩; fin_cases s <;> simp

/-- Todas las ternas de una familia de corridas. -/
def runsPart {n : ℕ} (R : Fin n → Run) : Finset (Finset ℤ) :=
  univ.biUnion fun r => (Ico 0 (R r).L).image (R r).tri

/-- Índices `(r, s, i)` de todos los elementos. -/
def runsIdx {n : ℕ} (R : Fin n → Run) : Finset (Fin n × Fin 3 × ℤ) :=
  univ.biUnion fun p : Fin n × Fin 3 =>
    (Ico 0 (R p.1).L).map ⟨fun i => (p.1, p.2, i), fun a b h => by simpa using h⟩

lemma mem_runsIdx {n : ℕ} {R : Fin n → Run} {q : Fin n × Fin 3 × ℤ} :
    q ∈ runsIdx R ↔ 0 ≤ q.2.2 ∧ q.2.2 < (R q.1).L := by
  obtain ⟨r, s, i⟩ := q
  simp only [runsIdx, mem_biUnion, mem_univ, true_and, mem_map, mem_Ico, Prod.exists]
  constructor
  · rintro ⟨r', s', i', ⟨h1, h2⟩, h⟩
    obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨r, s, i, ⟨h1, h2⟩, rfl⟩

lemma card_runsIdx {n : ℕ} (R : Fin n → Run) :
    (runsIdx R).card = ∑ p : Fin n × Fin 3, ((R p.1).L).toNat := by
  rw [runsIdx, card_biUnion]
  · simp
  · intro p _ p' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨i, -, rfl⟩ := mem_map.1 hq
    obtain ⟨i', -, h⟩ := mem_map.1 hq'
    have h' : (p'.1, p'.2, i') = (p.1, p.2, i) := h
    simp only [Prod.mk.injEq] at h'
    exact hne (Prod.ext h'.1.symm h'.2.1.symm)

/-- **Criterio de corridas.** Si todos los elementos caen en `X`, son distintos entre sí y son tantos
como `|X|`, entonces las ternas de las corridas parten `X` en ternas de suma −1. -/
theorem runs_isPart {n : ℕ} (R : Fin n → Run) (X : Finset ℤ)
    (hmem : ∀ r s i, 0 ≤ i → i < (R r).L → (R r).el i s ∈ X)
    (hinj : ∀ r r' s s' i i', 0 ≤ i → i < (R r).L → 0 ≤ i' → i' < (R r').L →
      (R r).el i s = (R r').el i' s' → r = r' ∧ s = s' ∧ i = i')
    (hcard : X.card = ∑ p : Fin n × Fin 3, ((R p.1).L).toNat) :
    IsPart (TS (-1)) X (runsPart R) := by
  set Φ : Fin n × Fin 3 × ℤ → ℤ := fun q => (R q.1).el q.2.2 q.2.1
  have hinjΦ : Set.InjOn Φ (runsIdx R) := by
    rintro ⟨r, s, i⟩ hq ⟨r', s', i'⟩ hq' h
    rw [mem_coe, mem_runsIdx] at hq hq'
    obtain ⟨rfl, rfl, rfl⟩ := hinj r r' s s' i i' hq.1 hq.2 hq'.1 hq'.2 h
    rfl
  have hsub : (runsIdx R).image Φ ⊆ X := by
    intro z hz
    obtain ⟨⟨r, s, i⟩, hq, rfl⟩ := mem_image.1 hz
    rw [mem_runsIdx] at hq
    exact hmem r s i hq.1 hq.2
  have himg : (runsIdx R).image Φ = X := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injOn hinjΦ, card_runsIdx, hcard]
  refine ⟨?_, ?_, ?_⟩
  · -- cada bloque es una terna de suma −1
    intro C hC
    simp only [runsPart, mem_biUnion, mem_univ, true_and, mem_image, mem_Ico] at hC
    obtain ⟨r, i, ⟨h0, hL⟩, rfl⟩ := hC
    have d : ∀ s s' : Fin 3, s ≠ s' → (R r).el i s ≠ (R r).el i s' := fun s s' hs h =>
      hs (hinj r r s s' i i h0 hL h0 hL h).2.1
    refine ⟨?_, ?_⟩
    · rw [Run.tri_eq]
      exact card_eq_three.2 ⟨_, _, _, d 0 1 (by decide), d 0 2 (by decide), d 1 2 (by decide), rfl⟩
    · rw [Run.tri_eq, sum_insert, sum_pair (d 1 2 (by decide))]
      · simp only [Run.el, id]; ring
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨d 0 1 (by decide), d 0 2 (by decide)⟩
  · -- disjuntos
    intro C hC C' hC' hne
    simp only [runsPart, mem_biUnion, mem_univ, true_and, mem_image, mem_Ico] at hC hC'
    obtain ⟨r, i, ⟨h0, hL⟩, rfl⟩ := hC
    obtain ⟨r', i', ⟨h0', hL'⟩, rfl⟩ := hC'
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨s, rfl⟩ := Run.mem_tri.1 hz
    obtain ⟨s', hs'⟩ := Run.mem_tri.1 hz'
    obtain ⟨rfl, -, rfl⟩ := hinj r r' s s' i i' h0 hL h0' hL' hs'.symm
    exact hne rfl
  · -- la unión es X
    rw [← himg]; ext z
    simp only [runsPart, mem_biUnion, mem_univ, true_and, mem_image, mem_Ico, id]
    constructor
    · rintro ⟨_, ⟨r, i, ⟨h0, hL⟩, rfl⟩, hz⟩
      obtain ⟨s, rfl⟩ := Run.mem_tri.1 hz
      exact ⟨(r, s, i), mem_runsIdx.2 ⟨h0, hL⟩, rfl⟩
    · rintro ⟨⟨r, s, i⟩, hq, rfl⟩
      rw [mem_runsIdx] at hq
      exact ⟨_, ⟨r, i, ⟨hq.1, hq.2⟩, rfl⟩, Run.mem_tri.2 ⟨s, rfl⟩⟩

end LemaB
