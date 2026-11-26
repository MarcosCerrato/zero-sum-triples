import Mathlib

/-!
# Particiones 3-buenas (Gurvich–Naumova)

Trabajamos en `ℤ` para evitar restas truncadas.
-/

namespace GN

open Finset

/-- Un bloque es 3-bueno si tiene a lo sumo 3 elementos y su suma es potencia de 3. -/
def Good (B : Finset ℤ) : Prop := B.card ≤ 3 ∧ ∃ k : ℕ, B.sum id = 3 ^ k

/-- Un triple de suma cero. -/
def ZS (B : Finset ℤ) : Prop := B.card = 3 ∧ B.sum id = 0

/-- `P` es una partición de `S` cuyos bloques cumplen `g`. -/
def IsPart (g : Finset ℤ → Prop) (S : Finset ℤ) (P : Finset (Finset ℤ)) : Prop :=
  (∀ B ∈ P, g B) ∧ (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧ P.biUnion id = S

lemma IsPart.subset {g} {S P} (h : IsPart g S P) {B} (hB : B ∈ P) : B ⊆ S := by
  rw [← h.2.2]; intro x hx; simp only [mem_biUnion, id]; exact ⟨B, hB, hx⟩

lemma IsPart.union {g} {S₁ S₂ P₁ P₂} (h₁ : IsPart g S₁ P₁) (h₂ : IsPart g S₂ P₂)
    (hd : Disjoint S₁ S₂) : IsPart g (S₁ ∪ S₂) (P₁ ∪ P₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB; rcases mem_union.1 hB with hB | hB
    · exact h₁.1 B hB
    · exact h₂.1 B hB
  · intro B hB C hC hBC
    rcases mem_union.1 hB with hB | hB <;> rcases mem_union.1 hC with hC | hC
    · exact h₁.2.1 B hB C hC hBC
    · exact hd.mono (h₁.subset hB) (h₂.subset hC)
    · exact (hd.mono (h₁.subset hC) (h₂.subset hB)).symm
    · exact h₂.2.1 B hB C hC hBC
  · rw [union_biUnion, h₁.2.2, h₂.2.2]

lemma IsPart.erase {g} {S P} (h : IsPart g S P) {T} (hT : T ∈ P) :
    IsPart g (S \ T) (P.erase T) := by
  refine ⟨fun B hB => h.1 B (mem_of_mem_erase hB),
    fun B hB C hC hBC => h.2.1 B (mem_of_mem_erase hB) C (mem_of_mem_erase hC) hBC, ?_⟩
  ext x; simp only [mem_biUnion, mem_erase, id, mem_sdiff]
  constructor
  · rintro ⟨B, ⟨hBT, hB⟩, hx⟩
    refine ⟨h.subset hB hx, fun hxT => ?_⟩
    exact Finset.disjoint_left.1 (h.2.1 B hB T hT hBT) hx hxT
  · rintro ⟨hxS, hxT⟩
    rw [← h.2.2] at hxS; simp only [mem_biUnion, id] at hxS
    obtain ⟨B, hB, hxB⟩ := hxS
    exact ⟨B, ⟨fun hBT => hxT (hBT ▸ hxB), hB⟩, hxB⟩

lemma IsPart.single {g} {B : Finset ℤ} (hB : g B) : IsPart g B {B} := by
  refine ⟨by simpa using hB, by simp, by simp⟩

lemma IsPart.empty {g} : IsPart g ∅ ∅ := ⟨by simp, by simp, by simp⟩

/-- Trasladar por `N = 3^t` una partición en triples de suma cero da bloques 3-buenos
(cada uno suma `3^(t+1)`). -/
lemma IsPart.shift {S P} (h : IsPart ZS S P) (t : ℕ) :
    IsPart Good (S.map (addLeftEmbedding ((3:ℤ) ^ t)))
      (P.image fun B => B.map (addLeftEmbedding ((3:ℤ) ^ t))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B' hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    obtain ⟨hc, hs⟩ := h.1 B hB
    refine ⟨by simp [hc], t + 1, ?_⟩
    rw [sum_map]
    simp only [addLeftEmbedding_apply, id]
    rw [sum_add_distrib, sum_const, hc]
    simp only [id] at hs; rw [hs]; ring
  · intro B' hB' C' hC' hne
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hC'
    have : B ≠ C := fun h' => hne (h' ▸ rfl)
    exact (Finset.disjoint_map _).2 (h.2.1 B hB C hC this)
  · rw [← h.2.2]; ext x
    simp only [mem_biUnion, mem_image, id, mem_map, addLeftEmbedding_apply]
    constructor
    · rintro ⟨_, ⟨B, hB, rfl⟩, hx⟩
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      exact ⟨y, ⟨B, hB, hy⟩, rfl⟩
    · rintro ⟨y, ⟨B, hB, hy⟩, rfl⟩
      exact ⟨_, ⟨B, hB, rfl⟩, mem_map.2 ⟨y, hy, rfl⟩⟩

end GN
