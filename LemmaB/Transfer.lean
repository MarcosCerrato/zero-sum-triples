import LemmaB.Defs

/-!
# Lema B: transferencia 3-ádica con bloque (0,0,0)

Ver `lemaB/PROOF.md`, §2. Con `m = 3k+1`:
* `S0 ∪ E = [−k..k]` (disjuntos), con una partición de `S0` en ternas de suma 0;
* `σ : A → B` biyección cuyos desplazamientos `σ x − x` recorren `E` biyectivamente;
* `X1 = [−k..k] ∖ A` y `X2 = [−k..k] ∖ B` partidos en ternas de suma `−1`.

Entonces `[−m..m]` se parte en ternas de suma 0: `3·S0`, `3·X1+1`, `−3·X2−1` y las ternas mixtas
`{3(σx−x), 3x+1, −3σx−1}`.
-/

namespace LemaB

open Finset GN

/-- Terna con suma `s`. -/
def TS (s : ℤ) (B : Finset ℤ) : Prop := B.card = 3 ∧ B.sum id = s

/-- Imagen de una partición por una inyección. -/
lemma IsPart.map {g g' : Finset ℤ → Prop} {S : Finset ℤ} {P : Finset (Finset ℤ)}
    (h : IsPart g S P) (e : ℤ ↪ ℤ) (hg : ∀ B, g B → g' (B.map e)) :
    IsPart g' (S.map e) (P.image fun B => B.map e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B' hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    exact hg B (h.1 B hB)
  · intro B' hB' C' hC' hne
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hC'
    have : B ≠ C := fun h' => hne (h' ▸ rfl)
    exact (Finset.disjoint_map _).2 (h.2.1 B hB C hC this)
  · rw [← h.2.2]; ext x
    simp only [mem_biUnion, mem_image, id, mem_map]
    constructor
    · rintro ⟨_, ⟨B, hB, rfl⟩, hx⟩
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      exact ⟨y, ⟨B, hB, hy⟩, rfl⟩
    · rintro ⟨y, ⟨B, hB, hy⟩, rfl⟩
      exact ⟨_, ⟨B, hB, rfl⟩, mem_map.2 ⟨y, hy, rfl⟩⟩

/-- `x ↦ 3x`. -/
def e0 : ℤ ↪ ℤ := ⟨fun x => 3 * x, fun a b h => by simp only at h; omega⟩
/-- `x ↦ 3x+1`. -/
def e1 : ℤ ↪ ℤ := ⟨fun x => 3 * x + 1, fun a b h => by simp only at h; omega⟩
/-- `x ↦ −3x−1`. -/
def e2 : ℤ ↪ ℤ := ⟨fun x => -3 * x - 1, fun a b h => by simp only at h; omega⟩

@[simp] lemma e0_apply (x : ℤ) : e0 x = 3 * x := rfl
@[simp] lemma e1_apply (x : ℤ) : e1 x = 3 * x + 1 := rfl
@[simp] lemma e2_apply (x : ℤ) : e2 x = -3 * x - 1 := rfl

lemma ts_map_affine {B : Finset ℤ} {s : ℤ} (hB : TS s B) (a b : ℤ) (e : ℤ ↪ ℤ)
    (he : ∀ x, e x = a * x + b) : TS (a * s + 3 * b) (B.map e) := by
  refine ⟨by rw [card_map]; exact hB.1, ?_⟩
  rw [sum_map]
  simp only [id, he]
  rw [sum_add_distrib, ← mul_sum, sum_const, hB.1]
  have := hB.2; simp only [id] at this; rw [this, nsmul_eq_mul]; push_cast; ring

lemma zs_e0 {B : Finset ℤ} (h : ZS B) : ZS (B.map e0) := by
  have := ts_map_affine (s := 0) h 3 0 e0 (fun x => by rw [e0_apply]; ring)
  exact ⟨this.1, by rw [this.2]; ring⟩

lemma zs_e1 {B : Finset ℤ} (h : TS (-1) B) : ZS (B.map e1) := by
  have := ts_map_affine h 3 1 e1 (fun x => by rw [e1_apply])
  exact ⟨this.1, by rw [this.2]; norm_num⟩

lemma zs_e2 {B : Finset ℤ} (h : TS (-1) B) : ZS (B.map e2) := by
  have := ts_map_affine h (-3) (-1) e2 (fun x => by rw [e2_apply]; ring)
  exact ⟨this.1, by rw [this.2]; norm_num⟩

/-- La terna mixta de `x`. -/
def blk (σ : ℤ → ℤ) (x : ℤ) : Finset ℤ := {3 * (σ x - x), 3 * x + 1, -3 * σ x - 1}

lemma blk_zs (σ : ℤ → ℤ) (x : ℤ) : ZS (blk σ x) := by
  have h1 : 3 * (σ x - x) ≠ 3 * x + 1 := by omega
  have h2 : 3 * (σ x - x) ≠ -3 * σ x - 1 := by omega
  have h3 : 3 * x + 1 ≠ -3 * σ x - 1 := by omega
  refine ⟨card_eq_three.2 ⟨_, _, _, h1, h2, h3, rfl⟩, ?_⟩
  unfold blk
  rw [sum_insert (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨h1, h2⟩), sum_pair h3]
  simp only [id]; ring

lemma mem_blk {σ : ℤ → ℤ} {x z : ℤ} :
    z ∈ blk σ x ↔ z = 3 * (σ x - x) ∨ z = 3 * x + 1 ∨ z = -3 * σ x - 1 := by
  simp [blk]

/-- Las ternas mixtas parten `3E ∪ (3A+1) ∪ (−3B−1)`. -/
lemma mixed_part {σ : ℤ → ℤ} {A B E : Finset ℤ}
    (hσ : Set.BijOn σ A B) (hd : Set.BijOn (fun x => σ x - x) A E) :
    IsPart ZS (E.map e0 ∪ A.map e1 ∪ B.map e2) (A.image (blk σ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨x, -, rfl⟩ := mem_image.1 hC
    exact blk_zs σ x
  · intro C hC C' hC' hne
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hC
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hC'
    rw [Finset.disjoint_left]
    intro z hz hz'
    apply hne
    have hxy : x = y := by
      rw [mem_blk] at hz hz'
      rcases hz with h | h | h <;> rcases hz' with h' | h' | h'
      · exact hd.injOn (mem_coe.2 hx) (mem_coe.2 hy) (by show σ x - x = σ y - y; omega)
      all_goals first
        | omega
        | exact hσ.injOn (mem_coe.2 hx) (mem_coe.2 hy) (by omega)
    rw [hxy]
  · ext z
    simp only [mem_biUnion, mem_image, id, mem_union, mem_map, e0_apply, e1_apply, e2_apply]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hz⟩
      rw [mem_blk] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨_, mem_coe.1 (hd.mapsTo (mem_coe.2 hx)), rfl⟩)
      · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
      · exact Or.inr ⟨σ x, mem_coe.1 (hσ.mapsTo (mem_coe.2 hx)), by ring⟩
    · rintro ((⟨e, he, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨b, hb, rfl⟩)
      · obtain ⟨x, hx, hxe⟩ := hd.surjOn (mem_coe.2 he)
        exact ⟨_, ⟨x, mem_coe.1 hx, rfl⟩, mem_blk.2 (Or.inl (by simp only at hxe; omega))⟩
      · exact ⟨_, ⟨a, ha, rfl⟩, mem_blk.2 (Or.inr (Or.inl rfl))⟩
      · obtain ⟨x, hx, hxb⟩ := hσ.surjOn (mem_coe.2 hb)
        exact ⟨_, ⟨x, mem_coe.1 hx, rfl⟩, mem_blk.2 (Or.inr (Or.inr (by rw [hxb])))⟩

/-- **Lema de transferencia** (PROOF.md §2). -/
theorem transfer (k : ℕ) {S0 E A B X1 X2 : Finset ℤ} {σ : ℤ → ℤ}
    {P0 P1 P2 : Finset (Finset ℤ)}
    (hSE : Disjoint S0 E) (hSEu : S0 ∪ E = Icc (-(k : ℤ)) k)
    (hA : Disjoint A X1) (hAu : A ∪ X1 = Icc (-(k : ℤ)) k)
    (hB : Disjoint B X2) (hBu : B ∪ X2 = Icc (-(k : ℤ)) k)
    (hσ : Set.BijOn σ A B) (hd : Set.BijOn (fun x => σ x - x) A E)
    (h0 : IsPart ZS S0 P0) (h1 : IsPart (TS (-1)) X1 P1) (h2 : IsPart (TS (-1)) X2 P2) :
    IsPart ZS (Icc (-(3 * k + 1 : ℤ)) (3 * k + 1))
      (P0.image (fun C => C.map e0) ∪ P1.image (fun C => C.map e1) ∪
        P2.image (fun C => C.map e2) ∪ A.image (blk σ)) := by
  have q0 := IsPart.map h0 e0 (fun _ h => zs_e0 h)
  have q1 := IsPart.map h1 e1 (fun _ h => zs_e1 h)
  have q2 := IsPart.map h2 e2 (fun _ h => zs_e2 h)
  have qm := mixed_part hσ hd
  -- membresía en [−k..k]
  have memK : ∀ x : ℤ, x ∈ Icc (-(k : ℤ)) k ↔ -(k : ℤ) ≤ x ∧ x ≤ k := fun x => mem_Icc
  have dSE := Finset.disjoint_left.1 hSE
  have dA := Finset.disjoint_left.1 hA
  have dB := Finset.disjoint_left.1 hB
  have q01 := q0.union q1 (by
    rw [Finset.disjoint_left]; intro z hz hz'
    obtain ⟨a, -, rfl⟩ := mem_map.1 hz; obtain ⟨b, -, hb⟩ := mem_map.1 hz'
    simp only [e0_apply, e1_apply] at hb; omega)
  have q012 := q01.union q2 (by
    rw [Finset.disjoint_left]; intro z hz hz'
    obtain ⟨b, -, rfl⟩ := mem_map.1 hz'
    rcases mem_union.1 hz with hz | hz <;> obtain ⟨a, -, ha⟩ := mem_map.1 hz <;>
      simp only [e0_apply, e1_apply, e2_apply] at ha <;> omega)
  have qall := q012.union qm (by
    rw [Finset.disjoint_left]; intro z hz hz'
    simp only [mem_union, mem_map, e0_apply, e1_apply, e2_apply] at hz hz'
    rcases hz with ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) <;>
      rcases hz' with ((⟨b, hb, hab⟩ | ⟨b, hb, hab⟩) | ⟨b, hb, hab⟩)
    all_goals first
      | omega
      | (have : a = b := by omega
         subst this
         first | exact dSE ha hb | exact dA hb ha | exact dB hb ha))
  convert qall using 1
  ext z
  simp only [mem_Icc, mem_union, mem_map, e0_apply, e1_apply, e2_apply]
  have hS : ∀ x, x ∈ S0 ∨ x ∈ E ↔ -(k : ℤ) ≤ x ∧ x ≤ k := fun x => by
    rw [← mem_union, hSEu, mem_Icc]
  have hA' : ∀ x, x ∈ A ∨ x ∈ X1 ↔ -(k : ℤ) ≤ x ∧ x ≤ k := fun x => by
    rw [← mem_union, hAu, mem_Icc]
  have hB' : ∀ x, x ∈ B ∨ x ∈ X2 ↔ -(k : ℤ) ≤ x ∧ x ≤ k := fun x => by
    rw [← mem_union, hBu, mem_Icc]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hz : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
    rcases hz with hz | hz | hz
    · obtain ⟨q, rfl⟩ : ∃ q, z = 3 * q := ⟨z / 3, by omega⟩
      rcases (hS q).2 ⟨by omega, by omega⟩ with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨q, h, rfl⟩))
      · exact Or.inr (Or.inl (Or.inl ⟨q, h, rfl⟩))
    · obtain ⟨q, rfl⟩ : ∃ q, z = 3 * q + 1 := ⟨z / 3, by omega⟩
      rcases (hA' q).2 ⟨by omega, by omega⟩ with h | h
      · exact Or.inr (Or.inl (Or.inr ⟨q, h, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨q, h, rfl⟩))
    · obtain ⟨q, rfl⟩ : ∃ q, z = -3 * q - 1 := ⟨-(z / 3) - 1, by omega⟩
      rcases (hB' q).2 ⟨by omega, by omega⟩ with h | h
      · exact Or.inr (Or.inr ⟨q, h, rfl⟩)
      · exact Or.inl (Or.inr ⟨q, h, rfl⟩)
  · rintro (((⟨q, h, rfl⟩ | ⟨q, h, rfl⟩) | ⟨q, h, rfl⟩) | ((⟨q, h, rfl⟩ | ⟨q, h, rfl⟩) | ⟨q, h, rfl⟩))
    · have := (hS q).1 (Or.inl h); omega
    · have := (hA' q).1 (Or.inr h); omega
    · have := (hB' q).1 (Or.inr h); omega
    · have := (hS q).1 (Or.inr h); omega
    · have := (hA' q).1 (Or.inl h); omega
    · have := (hB' q).1 (Or.inl h); omega

/-- La terna `{−c,0,c}` de la parte interna se convierte en `{−3c,0,3c}`. -/
lemma map_e0_triple (c : ℤ) : ({-c, 0, c} : Finset ℤ).map e0 = {-(3 * c), 0, 3 * c} := by
  ext z; simp only [mem_map, mem_insert, mem_singleton, e0_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; rcases ha with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨-c, by simp, by ring⟩
    · exact ⟨0, by simp, by ring⟩
    · exact ⟨c, by simp, rfl⟩

/-- **Lema B(m, b)**: `[−m..m]` se parte en ternas de suma 0 y `{−b, 0, b}` es una de ellas. -/
def LemmaB (m b : ℕ) : Prop :=
  ∃ P : Finset (Finset ℤ), IsPart ZS (Icc (-(m : ℤ)) m) P ∧ ({-(b : ℤ), 0, (b : ℤ)} : Finset ℤ) ∈ P

/-- Un **sistema X** para `[−k..k]` y el conjunto de desplazamientos `E` (PROOF.md §2). -/
structure XSys (k : ℕ) (E : Finset ℤ) where
  A : Finset ℤ
  B : Finset ℤ
  X1 : Finset ℤ
  X2 : Finset ℤ
  σ : ℤ → ℤ
  P1 : Finset (Finset ℤ)
  P2 : Finset (Finset ℤ)
  hA : Disjoint A X1
  hAu : A ∪ X1 = Icc (-(k : ℤ)) k
  hB : Disjoint B X2
  hBu : B ∪ X2 = Icc (-(k : ℤ)) k
  hσ : Set.BijOn σ A B
  hd : Set.BijOn (fun x => σ x - x) A E
  h1 : IsPart (TS (-1)) X1 P1
  h2 : IsPart (TS (-1)) X2 P2

/-- Transferencia en términos del Lema B: parte interna `S0 ∋ 0, ±c` + sistema X ⇒ Lema B(3k+1, 3c). -/
theorem lemmaB_of_xsys (k c : ℕ) {S0 E : Finset ℤ} {P0 : Finset (Finset ℤ)}
    (hSE : Disjoint S0 E) (hSEu : S0 ∪ E = Icc (-(k : ℤ)) k)
    (h0 : IsPart ZS S0 P0) (hc : ({-(c : ℤ), 0, (c : ℤ)} : Finset ℤ) ∈ P0) (X : XSys k E) :
    LemmaB (3 * k + 1) (3 * c) := by
  refine ⟨P0.image (fun C => C.map e0) ∪ X.P1.image (fun C => C.map e1) ∪
      X.P2.image (fun C => C.map e2) ∪ X.A.image (blk X.σ), ?_, ?_⟩
  · have := transfer k hSE hSEu X.hA X.hAu X.hB X.hBu X.hσ X.hd h0 X.h1 X.h2
    push_cast; exact this
  · refine mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_image.2 ⟨_, hc, ?_⟩)))
    rw [map_e0_triple]; push_cast; rfl

/-- **Caso principal**: Lema B(j, c) + sistema X con desplazamientos `[−k..k] ∖ [−j..j]` ⇒ Lema B(3k+1, 3c). -/
theorem lemmaB_main (k j c : ℕ) (hjk : j ≤ k) (hB : LemmaB j c)
    (X : XSys k (Icc (-(k : ℤ)) k \ Icc (-(j : ℤ)) j)) : LemmaB (3 * k + 1) (3 * c) := by
  obtain ⟨P0, h0, hc⟩ := hB
  refine lemmaB_of_xsys k c Finset.disjoint_sdiff ?_ h0 hc X
  rw [Finset.union_sdiff_of_subset]
  exact Finset.Icc_subset_Icc (by omega) (by omega)

/-- **Caso tope**: `±[1..n]` en ternas de suma 0 (= Lema B(n+1, n+1) sin su terna central),
`n < c ≤ k`, más un sistema X con desplazamientos `[−k..k] ∖ ([−n..n] ∪ {±c})` ⇒ Lema B(3k+1, 3c). -/
theorem lemmaB_top (k n c : ℕ) (hnc : n < c) (hck : c ≤ k) (hL : LemmaB (n + 1) (n + 1))
    (X : XSys k (Icc (-(k : ℤ)) k \ (Icc (-(n : ℤ)) n ∪ {-(c : ℤ), (c : ℤ)}))) :
    LemmaB (3 * k + 1) (3 * c) := by
  obtain ⟨Q, hQ, hm⟩ := hL
  -- quitamos la terna {−(n+1), 0, n+1} y agregamos {−c, 0, c}
  set T : Finset ℤ := {-((n + 1 : ℕ) : ℤ), 0, ((n + 1 : ℕ) : ℤ)}
  set U : Finset ℤ := {-(c : ℤ), 0, (c : ℤ)}
  have hQ' := hQ.erase hm
  have hsd : Icc (-((n + 1 : ℕ) : ℤ)) (n + 1 : ℕ) \ T = Icc (-(n : ℤ)) n \ {0} := by
    ext z; simp only [T, mem_sdiff, mem_Icc, mem_insert, mem_singleton]; push_cast; omega
  rw [hsd] at hQ'
  have hU : ZS U := by
    have h1 : -(c : ℤ) ≠ 0 := by omega
    have h2 : -(c : ℤ) ≠ c := by omega
    have h3 : (0 : ℤ) ≠ c := by omega
    refine ⟨card_eq_three.2 ⟨_, _, _, h1, h2, h3, rfl⟩, ?_⟩
    rw [sum_insert (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨h1, h2⟩), sum_pair h3]
    simp
  have hP0 := hQ'.union (IsPart.single hU) (by
    rw [Finset.disjoint_left]; intro z hz hz'
    simp only [U, mem_sdiff, mem_Icc, mem_singleton, mem_insert] at hz hz'; omega)
  refine lemmaB_of_xsys k c (S0 := Icc (-(n : ℤ)) n \ {0} ∪ U) ?_ ?_ hP0
    (mem_union_right _ (mem_singleton_self _)) X
  · rw [Finset.disjoint_left]; intro z hz hz'
    simp only [U, mem_union, mem_sdiff, mem_Icc, mem_singleton, mem_insert] at hz hz'; omega
  · ext z; simp only [U, mem_union, mem_sdiff, mem_Icc, mem_singleton, mem_insert]; omega

end LemaB
