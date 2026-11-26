import LemmaB.Builder

/-! Familias explícitas de sistemas X (generado por `lemaB/gen_lean.py`). -/

namespace LemaB
open Finset GN

set_option maxHeartbeats 4000000


/-- Familia `F2` (ver `lemaB/families.py`): `u = 1w+0`, `w ≥ 1`. -/
noncomputable def xsys_F2 (w : ℕ) (hw : 1 ≤ w) :
    XSys (3*w+2) (Icc (-(((3*w+2) : ℕ) : ℤ)) (((3*w+2) : ℕ) : ℤ) \ Icc (-(((3*w+1) : ℕ) : ℤ)) (((3*w+1) : ℕ) : ℤ)) := by
  refine xsysOf (3*w+2) ![(-1*(w:ℤ)-1), (3*(w:ℤ)+2)] ![(2*(w:ℤ)+1), (0)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-1*(w:ℤ)), (2*(w:ℤ)+1), ((w:ℤ)+1)⟩, ⟨(1), ((w:ℤ)+1), ((w:ℤ))⟩]
    ![⟨(-1*(w:ℤ)-1), (2*(w:ℤ)+2), ((w:ℤ)+1)⟩, ⟨(1), ((w:ℤ)+1), ((w:ℤ))⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F2o_top_k` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 1`. -/
noncomputable def xsys_F2o_top_k (w : ℕ) (hw : 1 ≤ w) :
    XSys (6*w+5) (Icc (-(((6*w+5) : ℕ) : ℤ)) (((6*w+5) : ℕ) : ℤ) \ (Icc (-(((6*w+3) : ℕ) : ℤ)) (((6*w+3) : ℕ) : ℤ) ∪ {-(((6*w+5) : ℕ) : ℤ), (((6*w+5) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+5) ![(-2*(w:ℤ)-2), (6*(w:ℤ)+5)] ![(4*(w:ℤ)+2), (1)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)-1), (4*(w:ℤ)+3), (2*(w:ℤ)+2)⟩, ⟨(1), (2*(w:ℤ)+2), (2*(w:ℤ)+1)⟩]
    ![⟨(-2*(w:ℤ)-2), (4*(w:ℤ)+4), (2*(w:ℤ)+2)⟩, ⟨(0), (2*(w:ℤ)+3), (1)⟩, ⟨(2), (4*(w:ℤ)+3), (1)⟩, ⟨(3), (2*(w:ℤ)+4), ((w:ℤ)-1)⟩, ⟨((w:ℤ)+2), ((w:ℤ)+3), (1)⟩, ⟨((w:ℤ)+4), (3*(w:ℤ)+3), ((w:ℤ)-1)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F2e_top_k` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 1`. -/
noncomputable def xsys_F2e_top_k (w : ℕ) (hw : 1 ≤ w) :
    XSys (6*w+2) (Icc (-(((6*w+2) : ℕ) : ℤ)) (((6*w+2) : ℕ) : ℤ) \ (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) ∪ {-(((6*w+2) : ℕ) : ℤ), (((6*w+2) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+2) ![(-1*(w:ℤ)), (5*(w:ℤ)+1)] ![(5*(w:ℤ)+1), (-1*(w:ℤ))] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)-1), (6*(w:ℤ)+1), (2)⟩, ⟨(-2*(w:ℤ)+1), (4*(w:ℤ)+1), ((w:ℤ)-1)⟩, ⟨(-1*(w:ℤ)+1), (5*(w:ℤ)+2), ((w:ℤ)-1)⟩, ⟨(0), (2*(w:ℤ)+1), ((w:ℤ)+1)⟩, ⟨((w:ℤ)+1), (5*(w:ℤ)), (1)⟩, ⟨((w:ℤ)+2), (3*(w:ℤ)+2), ((w:ℤ)-1)⟩]
    ![⟨(-2*(w:ℤ)-1), (6*(w:ℤ)+1), (2)⟩, ⟨(-2*(w:ℤ)+1), (4*(w:ℤ)+1), ((w:ℤ)-1)⟩, ⟨(-1*(w:ℤ)+1), (5*(w:ℤ)+2), ((w:ℤ)-1)⟩, ⟨(0), (2*(w:ℤ)+1), ((w:ℤ)+1)⟩, ⟨((w:ℤ)+1), (5*(w:ℤ)), (1)⟩, ⟨((w:ℤ)+2), (3*(w:ℤ)+2), ((w:ℤ)-1)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F0e` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 1`. -/
noncomputable def xsys_F0e (w : ℕ) (hw : 1 ≤ w) :
    XSys (6*w) (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) \ Icc (-(((6*w-2) : ℕ) : ℤ)) (((6*w-2) : ℕ) : ℤ)) := by
  refine xsysOf (6*w) ![(-2*(w:ℤ)-1), (4*(w:ℤ)-1), (-2*(w:ℤ)+1), (4*(w:ℤ))] ![(4*(w:ℤ)-1), (-2*(w:ℤ)-1), (4*(w:ℤ)), (-2*(w:ℤ)+1)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (6*(w:ℤ)), (1)⟩, ⟨(-2*(w:ℤ)+2), (4*(w:ℤ)+1), (2*(w:ℤ)-1)⟩, ⟨(1), (2*(w:ℤ)+1), ((w:ℤ)-1)⟩, ⟨((w:ℤ)), ((w:ℤ)+1), (1)⟩, ⟨((w:ℤ)+2), (3*(w:ℤ)), ((w:ℤ)-1)⟩]
    ![⟨(-2*(w:ℤ)), (6*(w:ℤ)), (1)⟩, ⟨(-2*(w:ℤ)+2), (4*(w:ℤ)+1), (2*(w:ℤ)-1)⟩, ⟨(1), (2*(w:ℤ)+1), ((w:ℤ)-1)⟩, ⟨((w:ℤ)), ((w:ℤ)+1), (1)⟩, ⟨((w:ℤ)+2), (3*(w:ℤ)), ((w:ℤ)-1)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F0o` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 2`. -/
noncomputable def xsys_F0o (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+3) (Icc (-(((6*w+3) : ℕ) : ℤ)) (((6*w+3) : ℕ) : ℤ) \ Icc (-(((6*w+1) : ℕ) : ℤ)) (((6*w+1) : ℕ) : ℤ)) := by
  refine xsysOf (6*w+3) ![(-2*(w:ℤ)-2), (4*(w:ℤ)), (-2*(w:ℤ)), (4*(w:ℤ)+3)] ![(4*(w:ℤ)), (-2*(w:ℤ)-2), (4*(w:ℤ)+3), (-2*(w:ℤ))] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)-1), (4*(w:ℤ)+4), (1)⟩, ⟨(-2*(w:ℤ)+1), (4*(w:ℤ)+5), (2*(w:ℤ)-1)⟩, ⟨(0), (4*(w:ℤ)+1), (2)⟩, ⟨(2), (2*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨((w:ℤ)), ((w:ℤ)+2), (2)⟩, ⟨((w:ℤ)+4), (3*(w:ℤ)+1), ((w:ℤ)-1)⟩]
    ![⟨(-2*(w:ℤ)-1), (4*(w:ℤ)+4), (1)⟩, ⟨(-2*(w:ℤ)+1), (4*(w:ℤ)+5), (2*(w:ℤ)-1)⟩, ⟨(0), (4*(w:ℤ)+1), (2)⟩, ⟨(2), (2*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨((w:ℤ)), ((w:ℤ)+2), (2)⟩, ⟨((w:ℤ)+4), (3*(w:ℤ)+1), ((w:ℤ)-1)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F0e_top_km1` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 1`. -/
noncomputable def xsys_F0e_top_km1 (w : ℕ) (hw : 1 ≤ w) :
    XSys (6*w) (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) \ (Icc (-(((6*w-3) : ℕ) : ℤ)) (((6*w-3) : ℕ) : ℤ) ∪ {-(((6*w-1) : ℕ) : ℤ), (((6*w-1) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w) ![(-6*(w:ℤ)), (-2*(w:ℤ)), (6*(w:ℤ)-1), (6*(w:ℤ))] ![(-2), (4*(w:ℤ)), (1), (0)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)+1), (4*(w:ℤ)-1), (2*(w:ℤ))⟩, ⟨(1), (2*(w:ℤ)), (2*(w:ℤ)-1)⟩]
    ![⟨(-2*(w:ℤ)-1), (4*(w:ℤ)+2), (2*(w:ℤ)-1)⟩, ⟨(-1), (4*(w:ℤ)+1), (1)⟩, ⟨(2), (2*(w:ℤ)), ((w:ℤ)-1)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+1), ((w:ℤ)-1)⟩, ⟨(3*(w:ℤ)-1), (3*(w:ℤ)), (1)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F0o_top_km1` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 2`. -/
noncomputable def xsys_F0o_top_km1 (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+3) (Icc (-(((6*w+3) : ℕ) : ℤ)) (((6*w+3) : ℕ) : ℤ) \ (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) ∪ {-(((6*w+2) : ℕ) : ℤ), (((6*w+2) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+3) ![(-2), (4*(w:ℤ)+2), (1), (0)] ![(-6*(w:ℤ)-3), (-2*(w:ℤ)-1), (6*(w:ℤ)+2), (6*(w:ℤ)+3)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)-2), (4*(w:ℤ)+4), (2*(w:ℤ))⟩, ⟨(-1), (4*(w:ℤ)), (1)⟩, ⟨(2), (2*(w:ℤ)+1), ((w:ℤ)-2)⟩, ⟨((w:ℤ)), (3*(w:ℤ)+1), ((w:ℤ)-1)⟩, ⟨(2*(w:ℤ)-1), (4*(w:ℤ)+3), (1)⟩, ⟨(2*(w:ℤ)), (4*(w:ℤ)+1), (1)⟩, ⟨(3*(w:ℤ)-1), (3*(w:ℤ)), (1)⟩]
    ![⟨(-2*(w:ℤ)), (4*(w:ℤ)+1), (2*(w:ℤ)+1)⟩, ⟨(1), (2*(w:ℤ)+1), (2*(w:ℤ))⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F0e_top_k` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 4`. -/
noncomputable def xsys_F0e_top_k (w : ℕ) (hw : 4 ≤ w) :
    XSys (6*w) (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) \ (Icc (-(((6*w-3) : ℕ) : ℤ)) (((6*w-3) : ℕ) : ℤ) ∪ {-(((6*w) : ℕ) : ℤ), (((6*w) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w) ![(-2*(w:ℤ)-1), (4*(w:ℤ)-3), (-2*(w:ℤ)+2), (4*(w:ℤ)+1)] ![(4*(w:ℤ)-3), (-2*(w:ℤ)-1), (4*(w:ℤ)+1), (-2*(w:ℤ)+2)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (4*(w:ℤ)+2), (2)⟩, ⟨(-2*(w:ℤ)+3), (4*(w:ℤ)+4), (2*(w:ℤ)-3)⟩, ⟨(0), (4*(w:ℤ)-2), (3)⟩, ⟨(3), (2*(w:ℤ)+3), ((w:ℤ)-4)⟩, ⟨((w:ℤ)-1), ((w:ℤ)+2), (3)⟩, ⟨((w:ℤ)+5), (3*(w:ℤ)-1), ((w:ℤ)-2)⟩]
    ![⟨(-2*(w:ℤ)), (4*(w:ℤ)+2), (2)⟩, ⟨(-2*(w:ℤ)+3), (4*(w:ℤ)+4), (2*(w:ℤ)-3)⟩, ⟨(0), (4*(w:ℤ)-2), (3)⟩, ⟨(3), (2*(w:ℤ)+3), ((w:ℤ)-4)⟩, ⟨((w:ℤ)-1), ((w:ℤ)+2), (3)⟩, ⟨((w:ℤ)+5), (3*(w:ℤ)-1), ((w:ℤ)-2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F0o_top_k` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 2`. -/
noncomputable def xsys_F0o_top_k (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+3) (Icc (-(((6*w+3) : ℕ) : ℤ)) (((6*w+3) : ℕ) : ℤ) \ (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) ∪ {-(((6*w+3) : ℕ) : ℤ), (((6*w+3) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+3) ![(-2*(w:ℤ)-2), (4*(w:ℤ)), (-2*(w:ℤ)+1), (4*(w:ℤ)+2)] ![(4*(w:ℤ)), (-2*(w:ℤ)-2), (4*(w:ℤ)+2), (-2*(w:ℤ)+1)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)-1), (6*(w:ℤ)+2), (2)⟩, ⟨(-2*(w:ℤ)+2), (4*(w:ℤ)+1), (1)⟩, ⟨(-2*(w:ℤ)+3), (4*(w:ℤ)+3), (2*(w:ℤ)-1)⟩, ⟨(2), (2*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨((w:ℤ)), ((w:ℤ)+2), (2)⟩, ⟨((w:ℤ)+4), (3*(w:ℤ)+1), ((w:ℤ)-1)⟩]
    ![⟨(-2*(w:ℤ)-1), (6*(w:ℤ)+2), (2)⟩, ⟨(-2*(w:ℤ)+2), (4*(w:ℤ)+1), (1)⟩, ⟨(-2*(w:ℤ)+3), (4*(w:ℤ)+3), (2*(w:ℤ)-1)⟩, ⟨(2), (2*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨((w:ℤ)), ((w:ℤ)+2), (2)⟩, ⟨((w:ℤ)+4), (3*(w:ℤ)+1), ((w:ℤ)-1)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1e` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 2`. -/
noncomputable def xsys_F1e (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+1) (Icc (-(((6*w+1) : ℕ) : ℤ)) (((6*w+1) : ℕ) : ℤ) \ Icc (-(((6*w-2) : ℕ) : ℤ)) (((6*w-2) : ℕ) : ℤ)) := by
  refine xsysOf (6*w+1) ![(6*(w:ℤ)-2), (-6*(w:ℤ)-1), (6*(w:ℤ)), (-6*(w:ℤ)), (6*(w:ℤ)+1), (-2*(w:ℤ)+1)] ![(-3), (-2), (0), (1), (2), (4*(w:ℤ)+1)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (6*(w:ℤ)-1), (1)⟩, ⟨(-2*(w:ℤ)+2), (4*(w:ℤ)-2), (2*(w:ℤ))⟩, ⟨(2), (2*(w:ℤ)-1), ((w:ℤ)-1)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)), ((w:ℤ)-2)⟩, ⟨(3*(w:ℤ)-2), (3*(w:ℤ)-1), (1)⟩]
    ![⟨(-2*(w:ℤ)-2), (4*(w:ℤ)+4), (2*(w:ℤ)-2)⟩, ⟨(-4), (4*(w:ℤ)+3), (1)⟩, ⟨(-1), (4*(w:ℤ)+2), (1)⟩, ⟨(3), (2*(w:ℤ)), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+2), ((w:ℤ)-1)⟩, ⟨(3*(w:ℤ)-2), (3*(w:ℤ)), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1o` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 2`. -/
noncomputable def xsys_F1o (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+4) (Icc (-(((6*w+4) : ℕ) : ℤ)) (((6*w+4) : ℕ) : ℤ) \ Icc (-(((6*w+1) : ℕ) : ℤ)) (((6*w+1) : ℕ) : ℤ)) := by
  refine xsysOf (6*w+4) ![(-6*(w:ℤ)-4), (-6*(w:ℤ)-3), (-2*(w:ℤ)-1), (6*(w:ℤ)+2), (6*(w:ℤ)+3), (6*(w:ℤ)+4)] ![(-1), (1), (4*(w:ℤ)+1), (-2), (0), (2)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (4*(w:ℤ)+1), (2*(w:ℤ)+1)⟩, ⟨(1), (2*(w:ℤ)+1), (2*(w:ℤ))⟩]
    ![⟨(-2*(w:ℤ)-3), (4*(w:ℤ)+6), (2*(w:ℤ)-1)⟩, ⟨(-4), (4*(w:ℤ)+4), (2)⟩, ⟨(3), (2*(w:ℤ)+1), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨(2*(w:ℤ)-1), (4*(w:ℤ)+2), (2)⟩, ⟨(3*(w:ℤ)-1), (3*(w:ℤ)+1), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1e_top_km2` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 2`. -/
noncomputable def xsys_F1e_top_km2 (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+1) (Icc (-(((6*w+1) : ℕ) : ℤ)) (((6*w+1) : ℕ) : ℤ) \ (Icc (-(((6*w-3) : ℕ) : ℤ)) (((6*w-3) : ℕ) : ℤ) ∪ {-(((6*w-1) : ℕ) : ℤ), (((6*w-1) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+1) ![(-6*(w:ℤ)-1), (-6*(w:ℤ)), (-2*(w:ℤ)), (6*(w:ℤ)-1), (6*(w:ℤ)), (6*(w:ℤ)+1)] ![(-3), (0), (4*(w:ℤ)+1), (-2), (2), (1)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)+1), (4*(w:ℤ)-1), (2*(w:ℤ))⟩, ⟨(1), (2*(w:ℤ)), (2*(w:ℤ)-1)⟩]
    ![⟨(-2*(w:ℤ)-2), (4*(w:ℤ)+4), (2*(w:ℤ)-2)⟩, ⟨(-4), (4*(w:ℤ)+3), (1)⟩, ⟨(-1), (4*(w:ℤ)+2), (1)⟩, ⟨(3), (2*(w:ℤ)), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+2), ((w:ℤ)-1)⟩, ⟨(3*(w:ℤ)-2), (3*(w:ℤ)), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1e_top_km1` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 3`. -/
noncomputable def xsys_F1e_top_km1 (w : ℕ) (hw : 3 ≤ w) :
    XSys (6*w+1) (Icc (-(((6*w+1) : ℕ) : ℤ)) (((6*w+1) : ℕ) : ℤ) \ (Icc (-(((6*w-3) : ℕ) : ℤ)) (((6*w-3) : ℕ) : ℤ) ∪ {-(((6*w) : ℕ) : ℤ), (((6*w) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+1) ![(-6*(w:ℤ)-1), (6*(w:ℤ)-3), (6*(w:ℤ)+1), (-6*(w:ℤ)), (6*(w:ℤ)), (-2*(w:ℤ)+2)] ![(-3), (-2), (0), (1), (2), (4*(w:ℤ)+1)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (6*(w:ℤ)-2), (2)⟩, ⟨(-2*(w:ℤ)+3), (4*(w:ℤ)-2), (2*(w:ℤ)-1)⟩, ⟨(2), (2*(w:ℤ)-2), ((w:ℤ)-1)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+1), ((w:ℤ)-3)⟩, ⟨(3*(w:ℤ)-3), (3*(w:ℤ)-1), (2)⟩]
    ![⟨(-2*(w:ℤ)-2), (4*(w:ℤ)+4), (2*(w:ℤ)-2)⟩, ⟨(-4), (4*(w:ℤ)+3), (1)⟩, ⟨(-1), (4*(w:ℤ)+2), (1)⟩, ⟨(3), (2*(w:ℤ)), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+2), ((w:ℤ)-1)⟩, ⟨(3*(w:ℤ)-2), (3*(w:ℤ)), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1e_top_k` (ver `lemaB/families.py`): `u = 2w+0`, `w ≥ 3`. -/
noncomputable def xsys_F1e_top_k (w : ℕ) (hw : 3 ≤ w) :
    XSys (6*w+1) (Icc (-(((6*w+1) : ℕ) : ℤ)) (((6*w+1) : ℕ) : ℤ) \ (Icc (-(((6*w-3) : ℕ) : ℤ)) (((6*w-3) : ℕ) : ℤ) ∪ {-(((6*w+1) : ℕ) : ℤ), (((6*w+1) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+1) ![(-6*(w:ℤ)-1), (6*(w:ℤ)-3), (-6*(w:ℤ)), (6*(w:ℤ)+1), (6*(w:ℤ)), (-2*(w:ℤ)+2)] ![(-3), (-2), (0), (1), (2), (4*(w:ℤ)+1)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (6*(w:ℤ)-2), (2)⟩, ⟨(-2*(w:ℤ)+3), (4*(w:ℤ)-2), (2*(w:ℤ)-1)⟩, ⟨(2), (2*(w:ℤ)-2), ((w:ℤ)-1)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+1), ((w:ℤ)-3)⟩, ⟨(3*(w:ℤ)-3), (3*(w:ℤ)-1), (2)⟩]
    ![⟨(-2*(w:ℤ)-2), (4*(w:ℤ)+4), (2*(w:ℤ)-2)⟩, ⟨(-4), (4*(w:ℤ)+3), (1)⟩, ⟨(-1), (4*(w:ℤ)+2), (1)⟩, ⟨(3), (2*(w:ℤ)), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+2), ((w:ℤ)-1)⟩, ⟨(3*(w:ℤ)-2), (3*(w:ℤ)), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1o_top_km2` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 2`. -/
noncomputable def xsys_F1o_top_km2 (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+4) (Icc (-(((6*w+4) : ℕ) : ℤ)) (((6*w+4) : ℕ) : ℤ) \ (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) ∪ {-(((6*w+2) : ℕ) : ℤ), (((6*w+2) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+4) ![(-6*(w:ℤ)-4), (-6*(w:ℤ)-3), (-2*(w:ℤ)), (6*(w:ℤ)+1), (6*(w:ℤ)+3), (6*(w:ℤ)+4)] ![(-1), (1), (4*(w:ℤ)+1), (-2), (2), (0)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)-1), (6*(w:ℤ)+2), (1)⟩, ⟨(-2*(w:ℤ)+1), (4*(w:ℤ)), ((w:ℤ))⟩, ⟨(-1*(w:ℤ)+1), (5*(w:ℤ)+1), ((w:ℤ))⟩, ⟨(1), (2*(w:ℤ)+1), ((w:ℤ))⟩, ⟨((w:ℤ)+1), (5*(w:ℤ)), (1)⟩, ⟨((w:ℤ)+2), (3*(w:ℤ)+1), ((w:ℤ)-1)⟩]
    ![⟨(-2*(w:ℤ)-3), (4*(w:ℤ)+6), (2*(w:ℤ)-1)⟩, ⟨(-4), (4*(w:ℤ)+4), (2)⟩, ⟨(3), (2*(w:ℤ)+1), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨(2*(w:ℤ)-1), (4*(w:ℤ)+2), (2)⟩, ⟨(3*(w:ℤ)-1), (3*(w:ℤ)+1), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1o_top_km1` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 2`. -/
noncomputable def xsys_F1o_top_km1 (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+4) (Icc (-(((6*w+4) : ℕ) : ℤ)) (((6*w+4) : ℕ) : ℤ) \ (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) ∪ {-(((6*w+3) : ℕ) : ℤ), (((6*w+3) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+4) ![(-6*(w:ℤ)-4), (-6*(w:ℤ)-3), (-2*(w:ℤ)-1), (6*(w:ℤ)+2), (6*(w:ℤ)+3), (6*(w:ℤ)+4)] ![(0), (-2), (4*(w:ℤ)+1), (1), (-1), (2)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (4*(w:ℤ)+1), (2*(w:ℤ)+1)⟩, ⟨(1), (2*(w:ℤ)+1), (2*(w:ℤ))⟩]
    ![⟨(-2*(w:ℤ)-3), (4*(w:ℤ)+6), (2*(w:ℤ)-1)⟩, ⟨(-4), (4*(w:ℤ)+4), (2)⟩, ⟨(3), (2*(w:ℤ)+1), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨(2*(w:ℤ)-1), (4*(w:ℤ)+2), (2)⟩, ⟨(3*(w:ℤ)-1), (3*(w:ℤ)+1), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega


/-- Familia `F1o_top_k` (ver `lemaB/families.py`): `u = 2w+1`, `w ≥ 2`. -/
noncomputable def xsys_F1o_top_k (w : ℕ) (hw : 2 ≤ w) :
    XSys (6*w+4) (Icc (-(((6*w+4) : ℕ) : ℤ)) (((6*w+4) : ℕ) : ℤ) \ (Icc (-(((6*w) : ℕ) : ℤ)) (((6*w) : ℕ) : ℤ) ∪ {-(((6*w+4) : ℕ) : ℤ), (((6*w+4) : ℕ) : ℤ)})) := by
  refine xsysOf (6*w+4) ![(-6*(w:ℤ)-4), (-6*(w:ℤ)-3), (-2*(w:ℤ)-1), (6*(w:ℤ)+2), (6*(w:ℤ)+3), (6*(w:ℤ)+4)] ![(-1), (-2), (4*(w:ℤ)+1), (1), (0), (2)] _ ?_ ?_ ?_ ?_ ?_ ?_
    ![⟨(-2*(w:ℤ)), (4*(w:ℤ)+1), (2*(w:ℤ)+1)⟩, ⟨(1), (2*(w:ℤ)+1), (2*(w:ℤ))⟩]
    ![⟨(-2*(w:ℤ)-3), (4*(w:ℤ)+6), (2*(w:ℤ)-1)⟩, ⟨(-4), (4*(w:ℤ)+4), (2)⟩, ⟨(3), (2*(w:ℤ)+1), ((w:ℤ)-2)⟩, ⟨((w:ℤ)+1), (3*(w:ℤ)+3), ((w:ℤ)-2)⟩, ⟨(2*(w:ℤ)-1), (4*(w:ℤ)+2), (2)⟩, ⟨(3*(w:ℤ)-1), (3*(w:ℤ)+1), (2)⟩] ?_ ?_
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · ext z; simp [Fin.exists_fin_succ]; omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega
  · apply runs_isPart
    · intro r s i h0 hL; fin_cases r <;> fin_cases s <;> simp [Run.el, Fin.exists_fin_succ] at hL ⊢ <;> omega
    · intro r r' s s' i i' h0 hL h0' hL' h
      fin_cases r <;> fin_cases r' <;> fin_cases s <;> fin_cases s' <;> simp [Run.el] at hL hL' h ⊢ <;> omega
    · rw [card_Icc_sdiff _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega) (by intro i; fin_cases i <;> simp <;> omega)]
      simp [Fin.sum_univ_succ, Fintype.sum_prod_type]; omega

end LemaB
