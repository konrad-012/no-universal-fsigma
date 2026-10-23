module

public import Mathlib

@[expose] public section

/-! Finite-coordinate matrix facts for algebraic tensor spans.

All rank bounds here are given by vanishing minors. In particular, no use is made of a
finite-dimensional `finrank` for an infinite-dimensional ambient space.
-/

namespace NoUniversalFSigma.Proof

open Set Matrix

namespace CoordinateMatrix

variable {I J X : Type*}

/-- A coordinate matrix has rank at most `r` if all its `(r+1)`-minors vanish. -/
def RankAtMost (r : ℕ) (M : Matrix I J ℝ) : Prop :=
  ∀ (rows : Fin (r + 1) → I) (cols : Fin (r + 1) → J), (M.submatrix rows cols).det = 0

/-- Vanishing-minor conditions are closed for any topology making coordinates continuous. -/
theorem isClosed_rankAtMost [TopologicalSpace X] (r : ℕ) (M : X → Matrix I J ℝ)
    (hM : ∀ i j, Continuous fun x => M x i j) : IsClosed {x | RankAtMost r (M x)} := by
  have hset : {x | RankAtMost r (M x)} =
      ⋂ rows : Fin (r + 1) → I, ⋂ cols : Fin (r + 1) → J,
        {x | ((M x).submatrix rows cols).det = 0} := by
    ext x
    simp [RankAtMost]
  rw [hset]
  apply isClosed_iInter
  intro rows
  apply isClosed_iInter
  intro cols
  apply isClosed_eq _ continuous_const
  exact (continuous_pi fun i => continuous_pi fun j => hM (rows i) (cols j)).matrix_det

/-- A sum of `r` elementary coordinate tensors has no nonzero minor of size `r+1`. -/
theorem rankAtMost_sum (r : ℕ) (u : Fin r → I → ℝ) (v : Fin r → J → ℝ) :
    RankAtMost r (fun i j => ∑ k, u k i * v k j) := by
  classical
  intro rows cols
  let A : Matrix (Fin (r + 1)) (Fin r) ℝ := fun i k => u k (rows i)
  let B : Matrix (Fin r) (Fin (r + 1)) ℝ := fun k j => v k (cols j)
  change (A * B).det = 0
  by_contra hdet
  have hrank := Matrix.rank_of_det_ne_zero hdet
  have hbound : (A * B).rank ≤ r :=
    (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_width A)
  simp only [Fintype.card_fin] at hrank
  omega

/-- Rank zero in the minor sense means that every coordinate vanishes. -/
theorem rankAtMost_zero_iff (M : Matrix I J ℝ) : RankAtMost 0 M ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    simpa [Matrix.det_fin_one] using
      h (fun _ => i) (fun _ => j)
  · rintro rfl rows cols
    simp

/-- A matrix of finite minor rank is either zero or admits an invertible maximal minor.
The least vanishing-minor bound supplies the minor, without assigning a possibly misleading
natural-number dimension to an infinite-dimensional column space. -/
theorem exists_maximal_minor (M : Matrix I J ℝ) (hfinite : ∃ r, RankAtMost r M) :
    M = 0 ∨ ∃ r : ℕ, 0 < r ∧ RankAtMost r M ∧
      ∃ (rows : Fin r → I) (cols : Fin r → J), (M.submatrix rows cols).det ≠ 0 := by
  classical
  let r := Nat.find hfinite
  have hr : RankAtMost r M := Nat.find_spec hfinite
  cases hr0 : r with
  | zero => exact Or.inl ((rankAtMost_zero_iff M).mp (hr0 ▸ hr))
  | succ k =>
    have hk : ¬ RankAtMost k M := Nat.find_min hfinite (by omega : k < r)
    simp only [RankAtMost, not_forall] at hk
    obtain ⟨rows, cols, hdet⟩ := hk
    exact Or.inr ⟨k + 1, by omega, hr0 ▸ hr, rows, cols, hdet⟩

/-- An invertible maximal coordinate minor reconstructs every matrix entry from its
selected rows and columns. This is the finite Schur-complement identity. -/
theorem reconstruct {r : ℕ} (M : Matrix I J ℝ) (hr : RankAtMost r M)
    (rows : Fin r → I) (cols : Fin r → J) (hdet : (M.submatrix rows cols).det ≠ 0)
    (i : I) (j : J) :
    M i j = ∑ s : Fin r, ∑ t : Fin r,
      M i (cols t) * (M.submatrix rows cols)⁻¹ t s * M (rows s) j := by
  classical
  let A := M.submatrix rows cols
  let B : Matrix (Fin r) (Fin 1) ℝ := fun s _ => M (rows s) j
  let C : Matrix (Fin 1) (Fin r) ℝ := fun _ t => M i (cols t)
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => M i j
  let augRows : Fin r ⊕ Fin 1 → I := Sum.elim rows (fun _ => i)
  let augCols : Fin r ⊕ Fin 1 → J := Sum.elim cols (fun _ => j)
  let e : Fin r ⊕ Fin 1 ≃ Fin (r + 1) := finSumFinEquiv
  have hminor := hr (augRows ∘ e.symm) (augCols ∘ e.symm)
  change ((M.submatrix augRows augCols).submatrix e.symm e.symm).det = 0 at hminor
  rw [Matrix.det_submatrix_equiv_self] at hminor
  have hblocks : M.submatrix augRows augCols = Matrix.fromBlocks A B C D := by
    ext a b
    cases a <;> cases b <;> rfl
  rw [hblocks] at hminor
  let : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.det_fromBlocks₁₁] at hminor
  have hzero : (D - C * ⅟A * B).det = 0 := (mul_eq_zero.mp hminor).resolve_left hdet
  rw [Matrix.det_fin_one, Matrix.sub_apply, Matrix.invOf_eq_nonsing_inv] at hzero
  have heq : M i j = (C * A⁻¹ * B) 0 0 := sub_eq_zero.mp hzero
  change M i j = ∑ s : Fin r,
    (∑ t : Fin r, M i (cols t) * A⁻¹ t s) * M (rows s) j at heq
  simpa only [Finset.sum_mul] using heq

end CoordinateMatrix

end NoUniversalFSigma.Proof
