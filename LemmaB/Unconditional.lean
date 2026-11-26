import LemmaB.Final
import LemmaB.GNLean.Universal

/-!
# Lema B sin hipótesis

El caso `3 ∤ b` sale de `GNL.displacement_permutations` y `GNL.zeroPartition_hole_of_displacement`,
portados de JD-Jones-ASES/gn-lean (MIT; ver `LemmaB/GNLean/LICENSE`).
-/

namespace LemaB

open Finset GN

theorem lemmaB_not_dvd :
    ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → 1 ≤ b → b ≤ m → b % 3 ≠ 0 → LemmaB m b := by
  intro m b hm h10 hb1 hbm h3
  set k : ℤ := (((m - 1) / 3 : ℕ) : ℤ) with hk
  have hmk : (m : ℤ) = 3 * k + 1 := by omega
  have hk3 : 3 ≤ k := by omega
  -- b = 3j+1 o b = −(3j+1)
  obtain ⟨j, ha, hj⟩ : ∃ j : ℤ, ((b : ℤ) = 3 * j + 1 ∨ (b : ℤ) = -(3 * j + 1)) ∧ -k ≤ j ∧ j ≤ k := by
    rcases (show b % 3 = 1 ∨ b % 3 = 2 by omega) with h | h
    · exact ⟨(((b - 1) / 3 : ℕ) : ℤ), Or.inl (by omega), by omega, by omega⟩
    · exact ⟨-(((b + 1) / 3 : ℕ) : ℤ), Or.inr (by omega), by omega, by omega⟩
  obtain ⟨σ, hσ⟩ := GNL.displacement_permutations hk3 hj
  have hZ := GNL.zeroPartition_hole_of_displacement ha hσ
  set P' := (GNL.displacementDomain k j).image (GNL.residueTriple σ)
  set T : Finset ℤ := {-(b : ℤ), 0, (b : ℤ)}
  have hP' : IsPart ZS (GNL.holeVertices k b) P' :=
    ⟨fun B hB => ⟨(hZ.2.2 B hB).1, (hZ.2.2 B hB).2⟩, hZ.2.1, hZ.1⟩
  have hT : ZS T := by
    have h1 : -(b : ℤ) ≠ 0 := by omega
    have h2 : -(b : ℤ) ≠ b := by omega
    have h3' : (0 : ℤ) ≠ b := by omega
    refine ⟨card_eq_three.2 ⟨_, _, _, h1, h2, h3', rfl⟩, ?_⟩
    rw [sum_insert (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨h1, h2⟩), sum_pair h3']
    simp
  have hU := hP'.union (IsPart.single hT) (by
    rw [Finset.disjoint_left]; intro z hz hz'
    simp only [GNL.holeVertices, T, mem_erase, mem_insert, mem_singleton] at hz hz'
    omega)
  refine ⟨P' ∪ {T}, ?_, mem_union_right _ (mem_singleton_self T)⟩
  convert hU using 1
  ext z
  simp only [GNL.holeVertices, T, mem_union, mem_erase, mem_Icc, mem_insert, mem_singleton]
  omega

/-- **Lema B, sin hipótesis**: para todo `m ≡ 1 (mod 3)` con `m ≥ 10` y todo `b ∈ [1..m]`,
`[−m..m]` se parte en ternas de suma 0 con `{−b, 0, b}` como una de ellas. -/
theorem lemmaB : ∀ m b : ℕ, m % 3 = 1 → 10 ≤ m → 1 ≤ b → b ≤ m → LemmaB m b :=
  lemmaB_of_not_dvd lemmaB_not_dvd

end LemaB
