import LemmaB.Transfer

/-!
# Certificados: chequeo computable de una partición explícita

`checkB m b L = true` (calculado con `decide`) prueba `LemmaB m b`. `L` es una lista de ternas.
-/

namespace LemaB

open Finset GN

/-- `[−m, …, m]` en orden. -/
def sortedRange (m : ℕ) : List ℤ := (List.range (2 * m + 1)).map fun i : ℕ => (i : ℤ) - (m : ℤ)

/-- Chequeo: ternas de suma 0, que juntas son exactamente `[−m..m]`, y una de ellas es `[−b, 0, b]`. -/
def checkB (m b : ℕ) (L : List (List ℤ)) : Bool :=
  L.all (fun t => t.length == 3 && t.sum == 0) &&
  (L.flatten.insertionSort (· ≤ ·) == sortedRange m) &&
  L.contains [-(b : ℤ), 0, (b : ℤ)]

lemma mem_sortedRange {m : ℕ} {z : ℤ} : z ∈ sortedRange m ↔ -(m : ℤ) ≤ z ∧ z ≤ m := by
  simp only [sortedRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨(z + m).toNat, by omega, by omega⟩

lemma nodup_sortedRange (m : ℕ) : (sortedRange m).Nodup :=
  (List.nodup_range).map (fun a b h => by simpa using h)

theorem lemmaB_of_check {m b : ℕ} {L : List (List ℤ)} (h : checkB m b L = true) : LemmaB m b := by
  simp only [checkB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨hall, hsort⟩, hcont⟩ := h
  have hperm : L.flatten.Perm (sortedRange m) := by
    rw [← hsort]; exact (List.perm_insertionSort _ _).symm
  have hnod : L.flatten.Nodup := hperm.nodup_iff.2 (nodup_sortedRange m)
  rw [List.nodup_flatten] at hnod
  obtain ⟨hnodt, hpw⟩ := hnod
  refine ⟨(L.map List.toFinset).toFinset, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro B hB
    simp only [List.mem_toFinset, List.mem_map] at hB
    obtain ⟨t, ht, rfl⟩ := hB
    obtain ⟨hl, hs⟩ := hall t ht
    refine ⟨by rw [List.toFinset_card_of_nodup (hnodt t ht)]; exact hl, ?_⟩
    rw [List.sum_toFinset _ (hnodt t ht)]; simpa using hs
  · intro B hB C hC hne
    simp only [List.mem_toFinset, List.mem_map] at hB hC
    obtain ⟨t, ht, rfl⟩ := hB
    obtain ⟨t', ht', rfl⟩ := hC
    have htt : t ≠ t' := fun h => hne (h ▸ rfl)
    have := hpw.forall ht ht' htt
    exact List.disjoint_toFinset_iff_disjoint.2 this
  · ext z
    simp only [mem_biUnion, List.mem_toFinset, List.mem_map, id, mem_Icc]
    rw [← mem_sortedRange, ← hperm.mem_iff, List.mem_flatten]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, hz⟩; exact ⟨t, ht, List.mem_toFinset.1 hz⟩
    · rintro ⟨t, ht, hz⟩; exact ⟨_, ⟨t, ht, rfl⟩, List.mem_toFinset.2 hz⟩
  · simp only [List.mem_toFinset, List.mem_map]
    exact ⟨_, hcont, by ext z; simp⟩

/-- Ejemplo: Lema B(10, 6). -/
example : LemmaB 10 6 := lemmaB_of_check (L := [[10, -3, -7], [-9, 4, 5], [-10, 2, 8], [-4, 1, 3], [7, -2, -5], [9, -1, -8], [-6, 0, 6]]) (by decide)

end LemaB
