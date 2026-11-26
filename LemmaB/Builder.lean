import LemmaB.Runs

/-!
# Armado de un sistema X a partir de datos explícitos

`σ` se da por dos listas `a b : Fin m → ℤ` (`σ (a i) = b i`). Las ternas de `X1 = [−k..k] ∖ A` y de
`X2 = [−k..k] ∖ B` se dan por corridas (`Runs.lean`).
-/

namespace LemaB

open Finset GN

/-- `σ (a i) = b i`; fuera de `A` es la identidad (no importa). -/
noncomputable def sigOf {m : ℕ} (a b : Fin m → ℤ) (x : ℤ) : ℤ := by
  classical
  exact if h : ∃ i, a i = x then b (Classical.choose h) else x

lemma sigOf_apply {m : ℕ} {a b : Fin m → ℤ} (ha : Function.Injective a) (i : Fin m) :
    sigOf a b (a i) = b i := by
  classical
  have h : ∃ j, a j = a i := ⟨i, rfl⟩
  simp only [sigOf, h, dite_true]
  rw [ha (Classical.choose_spec h)]

/-- Constructor de sistemas X a partir de datos explícitos. -/
noncomputable def xsysOf (k : ℕ) {m n1 n2 : ℕ} (a b : Fin m → ℤ) (E : Finset ℤ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hd : Function.Injective fun i => b i - a i)
    (hE : univ.image (fun i => b i - a i) = E)
    (haK : ∀ i, a i ∈ Icc (-(k : ℤ)) k) (hbK : ∀ i, b i ∈ Icc (-(k : ℤ)) k)
    (R1 : Fin n1 → Run) (R2 : Fin n2 → Run)
    (h1 : IsPart (TS (-1)) (Icc (-(k : ℤ)) k \ univ.image a) (runsPart R1))
    (h2 : IsPart (TS (-1)) (Icc (-(k : ℤ)) k \ univ.image b) (runsPart R2)) : XSys k E where
  A := univ.image a
  B := univ.image b
  X1 := Icc (-(k : ℤ)) k \ univ.image a
  X2 := Icc (-(k : ℤ)) k \ univ.image b
  σ := sigOf a b
  P1 := runsPart R1
  P2 := runsPart R2
  hA := disjoint_sdiff
  hAu := union_sdiff_of_subset (fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx; exact haK i)
  hB := disjoint_sdiff
  hBu := union_sdiff_of_subset (fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx; exact hbK i)
  hσ := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
      rw [sigOf_apply ha]; exact mem_coe.2 (mem_image_of_mem _ (mem_univ _))
    · intro x hx y hy h
      obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
      obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
      rw [sigOf_apply ha, sigOf_apply ha] at h
      rw [hb h]
    · intro y hy
      obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
      exact ⟨a i, mem_coe.2 (mem_image_of_mem _ (mem_univ _)), sigOf_apply ha i⟩
  hd := by
    subst hE
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
      simp only [sigOf_apply ha]; exact mem_coe.2 (mem_image_of_mem _ (mem_univ _))
    · intro x hx y hy h
      obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
      obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
      simp only [sigOf_apply ha] at h
      rw [hd h]
    · intro y hy
      obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
      exact ⟨a i, mem_coe.2 (mem_image_of_mem _ (mem_univ _)), by simp only [sigOf_apply ha]⟩
  h1 := h1
  h2 := h2

/-- Tamaño de `[−k..k] ∖ A` cuando `A ⊆ [−k..k]` viene dado por una lista inyectiva. -/
lemma card_Icc_sdiff {k : ℕ} {m : ℕ} (a : Fin m → ℤ) (ha : Function.Injective a)
    (haK : ∀ i, a i ∈ Icc (-(k : ℤ)) k) :
    (Icc (-(k : ℤ)) k \ univ.image a).card = 2 * k + 1 - m := by
  rw [card_sdiff_of_subset (fun x hx => by obtain ⟨i, -, rfl⟩ := mem_image.1 hx; exact haK i),
    card_image_of_injective _ ha, card_univ, Fintype.card_fin, Int.card_Icc]
  omega

end LemaB
