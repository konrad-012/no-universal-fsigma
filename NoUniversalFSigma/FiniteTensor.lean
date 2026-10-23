module

public import NoUniversalFSigma.TensorCoordinates
public import NoUniversalFSigma.TensorCover

@[expose] public section

/-! Finite algebraic tensor spans of `Fσ` subspaces are `Fσ` (Wang, Lemma 6.1).
The ambient completed tensor space is represented by its square-summable coordinates.
-/

namespace NoUniversalFSigma.Proof

open Set NoUniversalFSigma CoordinateMatrix
open scoped lp

variable {I J : Type*}

@[simp]
theorem hilbertTensor_zero_left (y : ℓ²(J, ℝ)) :
    hilbertTensor (0 : ℓ²(I, ℝ)) y = 0 := by
  ext p
  simp [hilbertTensor_apply]

@[simp]
theorem hilbertTensor_zero_right (x : ℓ²(I, ℝ)) :
    hilbertTensor x (0 : ℓ²(J, ℝ)) = 0 := by
  ext p
  simp [hilbertTensor_apply]

/-- The algebraic tensor span, inside the completed coordinate Hilbert tensor space. -/
noncomputable def algebraicTensorSpan (H : Submodule ℝ ℓ²(I, ℝ))
    (K : Submodule ℝ ℓ²(J, ℝ)) : Submodule ℝ ℓ²(I × J, ℝ) :=
  Submodule.span ℝ (range fun p : H × K => hilbertTensor (p.1 : ℓ²(I, ℝ)) (p.2 : ℓ²(J, ℝ)))

theorem hilbertTensor_mem_algebraicTensorSpan (H : Submodule ℝ ℓ²(I, ℝ))
    (K : Submodule ℝ ℓ²(J, ℝ)) {u : ℓ²(I, ℝ)} {v : ℓ²(J, ℝ)} (hu : u ∈ H) (hv : v ∈ K) :
    hilbertTensor u v ∈ algebraicTensorSpan H K :=
  Submodule.subset_span ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩

/-- Scalar coefficients can be absorbed into the first factor of a finite tensor sum. -/
theorem mem_algebraicTensorSpan_iff (H : Submodule ℝ ℓ²(I, ℝ))
    (K : Submodule ℝ ℓ²(J, ℝ)) (z : ℓ²(I × J, ℝ)) :
    z ∈ algebraicTensorSpan H K ↔
      ∃ (r : ℕ) (u : Fin r → ℓ²(I, ℝ)) (v : Fin r → ℓ²(J, ℝ)),
        (∀ k, u k ∈ H) ∧ (∀ k, v k ∈ K) ∧ ∑ k, hilbertTensor (u k) (v k) = z := by
  classical
  constructor
  · intro hz
    obtain ⟨r, c, g, hg⟩ := Submodule.mem_span_set'.mp hz
    choose p hp using fun k : Fin r => (g k).2
    refine ⟨r, fun k => c k • (p k).1.val, fun k => (p k).2.val,
      fun k => H.smul_mem _ (p k).1.2, fun k => (p k).2.2, ?_⟩
    simpa only [hilbertTensor_smul_left, hp] using hg
  · rintro ⟨r, u, v, hu, hv, rfl⟩
    exact Submodule.sum_mem _ fun k _ => hilbertTensor_mem_algebraicTensorSpan H K (hu k) (hv k)

theorem column_mem_of_mem_algebraicTensorSpan (H : Submodule ℝ ℓ²(I, ℝ))
    (K : Submodule ℝ ℓ²(J, ℝ)) {z : ℓ²(I × J, ℝ)} (hz : z ∈ algebraicTensorSpan H K) (j : J) :
    hilbertColumn j z ∈ H := by
  obtain ⟨r, u, v, hu, hv, rfl⟩ := (mem_algebraicTensorSpan_iff H K z).mp hz
  rw [map_sum]
  exact H.sum_mem fun k _ => by rw [hilbertColumn_tensor]; exact H.smul_mem _ (hu k)

theorem row_mem_of_mem_algebraicTensorSpan (H : Submodule ℝ ℓ²(I, ℝ))
    (K : Submodule ℝ ℓ²(J, ℝ)) {z : ℓ²(I × J, ℝ)} (hz : z ∈ algebraicTensorSpan H K) (i : I) :
    hilbertRow i z ∈ K := by
  obtain ⟨r, u, v, hu, hv, rfl⟩ := (mem_algebraicTensorSpan_iff H K z).mp hz
  rw [map_sum]
  exact K.sum_mem fun k _ => by rw [hilbertRow_tensor]; exact K.smul_mem _ (hv k)

theorem finiteRank_of_mem_algebraicTensorSpan (H : Submodule ℝ ℓ²(I, ℝ))
    (K : Submodule ℝ ℓ²(J, ℝ)) {z : ℓ²(I × J, ℝ)} (hz : z ∈ algebraicTensorSpan H K) :
    ∃ r, RankAtMost r (fun i j => z (i, j)) := by
  obtain ⟨r, u, v, hu, hv, rfl⟩ := (mem_algebraicTensorSpan_iff H K z).mp hz
  refine ⟨r, ?_⟩
  simpa only [lp.coeFn_sum, Finset.sum_apply, hilbertTensor_apply] using rankAtMost_sum r
    (fun k i => u k i) (fun k j => v k j)

/-- Every finite-minor chart belongs to the algebraic tensor span, by reconstruction. -/
theorem minorChart_subset_algebraicTensorSpan
    (H : Submodule ℝ ℓ²(I, ℝ)) (K : Submodule ℝ ℓ²(J, ℝ))
    (C : ℕ → Set ℓ²(I, ℝ)) (D : ℕ → Set ℓ²(J, ℝ))
    (hC : ∀ n, C n ⊆ H) (hD : ∀ n, D n ⊆ K) (d : ChartIndex I J) :
    minorChart (fun z i j => z (i, j)) (fun j z => hilbertColumn j z)
      (fun i z => hilbertRow i z) C D d ⊆ algebraicTensorSpan H K := by
  classical
  intro z hz
  obtain ⟨hrank, hbound, hcolumns, hrows⟩ := hz
  have hdet : (Matrix.submatrix (fun i j => z (i, j)) d.rows d.cols).det ≠ 0 := by
    intro hzero
    have hpos : (0 : ℝ) < 1 / (d.detBound + 1 : ℝ) := by positivity
    simp only [hzero, abs_zero] at hbound
    linarith
  let A : Matrix (Fin d.size) (Fin d.size) ℝ :=
    Matrix.submatrix (fun i j => z (i, j)) d.rows d.cols
  have heq : z = ∑ s : Fin d.size, ∑ t : Fin d.size,
      A⁻¹ t s • hilbertTensor (hilbertColumn (d.cols t) z) (hilbertRow (d.rows s) z) := by
    ext ⟨i, j⟩
    have h := reconstruct (fun i j => z (i, j)) hrank d.rows d.cols hdet i j
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      hilbertTensor_apply, hilbertColumn_apply, hilbertRow_apply, smul_eq_mul]
    convert h using 1
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    dsimp [A]
    ring
  rw [heq]
  apply Submodule.sum_mem
  intro s _
  apply Submodule.sum_mem
  intro t _
  apply Submodule.smul_mem
  exact hilbertTensor_mem_algebraicTensorSpan H K
    (hC _ (hcolumns t)) (hD _ (hrows s))

/-- The algebraic tensor product of two `Fσ` real linear subspaces is `Fσ` in the
completed coordinate Hilbert tensor product. -/
theorem isSigma02_algebraicTensorSpan [Countable I] [Countable J]
    (H : Submodule ℝ ℓ²(I, ℝ)) (K : Submodule ℝ ℓ²(J, ℝ))
    (hH : IsSigma02 (H : Set ℓ²(I, ℝ))) (hK : IsSigma02 (K : Set ℓ²(J, ℝ))) :
    IsSigma02 (algebraicTensorSpan H K : Set ℓ²(I × J, ℝ)) := by
  classical
  obtain ⟨C, hC, hCeq⟩ := hH
  obtain ⟨D, hD, hDeq⟩ := hK
  have hCsub : ∀ n, C n ⊆ H := by
    intro n
    rw [hCeq]
    exact subset_iUnion C n
  have hDsub : ∀ n, D n ⊆ K := by
    intro n
    rw [hDeq]
    exact subset_iUnion D n
  have heq : (algebraicTensorSpan H K : Set ℓ²(I × J, ℝ)) =
      ⋃ d : ChartIndex I J,
        minorChart (fun z i j => z (i, j)) (fun j z => hilbertColumn j z)
          (fun i z => hilbertRow i z) C D d := by
    apply subset_antisymm
    · intro z hz
      apply mem_iUnion_minorChart_of_finiteRank
        (fun z i j => z (i, j)) (fun j z => hilbertColumn j z) (fun i z => hilbertRow i z)
        C D z (finiteRank_of_mem_algebraicTensorSpan H K hz)
      · intro j
        rw [← hCeq]
        exact column_mem_of_mem_algebraicTensorSpan H K hz j
      · intro i
        rw [← hDeq]
        exact row_mem_of_mem_algebraicTensorSpan H K hz i
    · exact iUnion_subset fun d => minorChart_subset_algebraicTensorSpan H K C D hCsub hDsub d
  rw [heq]
  exact isSigma02_iUnion_minorChart (fun z i j => z (i, j))
    (fun j z => hilbertColumn j z) (fun i z => hilbertRow i z)
    (fun i j => (lp.evalCLM ℝ (fun _ : I × J => ℝ) 2 (i, j)).continuous)
    (fun j => (hilbertColumn j).continuous) (fun i => (hilbertRow i).continuous) C D hC hD

/-- Taking algebraic spans in each factor gives the span of elementary tensors of the
original generators. -/
theorem algebraicTensorSpan_span_range {P Q : Type*}
    (u : P → ℓ²(I, ℝ)) (v : Q → ℓ²(J, ℝ)) :
    algebraicTensorSpan (Submodule.span ℝ (range u)) (Submodule.span ℝ (range v)) =
      Submodule.span ℝ (range fun p : P × Q => hilbertTensor (u p.1) (v p.2)) := by
  classical
  let T := Submodule.span ℝ (range fun p : P × Q => hilbertTensor (u p.1) (v p.2))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨⟨x, y⟩, rfl⟩
    have hxy : ∀ x ∈ Submodule.span ℝ (range u), ∀ y ∈ Submodule.span ℝ (range v),
        hilbertTensor x y ∈ T := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨q, rfl⟩ := hy
          exact Submodule.subset_span ⟨(p, q), rfl⟩
        | zero => simp
        | add y z _ _ hy hz => simpa using T.add_mem hy hz
        | smul a y _ hy => simpa using T.smul_mem a hy
      | zero => intro y _; simp
      | add x z _ _ hx hz =>
        intro y hy
        simpa using T.add_mem (hx y hy) (hz y hy)
      | smul a x _ hx =>
        intro y hy
        simpa using T.smul_mem a (hx y hy)
    exact hxy x.1 x.2 y.1 y.2
  · apply Submodule.span_le.mpr
    rintro z ⟨⟨p, q⟩, rfl⟩
    exact hilbertTensor_mem_algebraicTensorSpan _ _
      (Submodule.subset_span ⟨p, rfl⟩) (Submodule.subset_span ⟨q, rfl⟩)

end NoUniversalFSigma.Proof
