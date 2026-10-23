module

public import NoUniversalFSigma.TensorCoordinates

@[expose] public section

/-! Disjoint Hilbert coordinates and their finitely supported linear functionals. -/

namespace NoUniversalFSigma.Proof

open Set Topology
open scoped lp

variable {I J : Type*}

/-- Concatenate two square-summable families on disjoint coordinate sets. -/
noncomputable def hilbertJoinVector (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) : ℓ²(I ⊕ J, ℝ) :=
  ⟨Sum.elim x y, memℓp_gen (Summable.sum _
    (by simpa [Function.comp_def] using hilbert_summable_sq x)
    (by simpa [Function.comp_def] using hilbert_summable_sq y))⟩

@[simp] theorem hilbertJoinVector_inl (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) (i : I) :
    hilbertJoinVector x y (.inl i) = x i := rfl

@[simp] theorem hilbertJoinVector_inr (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) (j : J) :
    hilbertJoinVector x y (.inr j) = y j := rfl

theorem norm_hilbertJoinVector_sq (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    ‖hilbertJoinVector x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [hilbert_norm_sq, Summable.tsum_sum]
  · simp only [hilbertJoinVector_inl, hilbertJoinVector_inr, ← hilbert_norm_sq]
  · simpa [Function.comp_def] using hilbert_summable_sq x
  · simpa [Function.comp_def] using hilbert_summable_sq y

theorem norm_hilbertJoinVector_le (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    ‖hilbertJoinVector x y‖ ≤ ‖x‖ + ‖y‖ := by
  have h := norm_hilbertJoinVector_sq x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (hilbertJoinVector x y)]

/-- Concatenation is a continuous linear map for the usual product topology. -/
noncomputable def hilbertJoinCLM : (ℓ²(I, ℝ) × ℓ²(J, ℝ)) →L[ℝ] ℓ²(I ⊕ J, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun p => hilbertJoinVector p.1 p.2
      map_add' := by intro p q; ext (i | j) <;> rfl
      map_smul' := by intro c p; ext (i | j) <;> rfl }
    2 (fun p => (norm_hilbertJoinVector_le p.1 p.2).trans (by
      have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      linarith))

/-- The first coordinate projection from a disjoint Hilbert sum. -/
noncomputable def hilbertLeft : ℓ²(I ⊕ J, ℝ) →L[ℝ] ℓ²(I, ℝ) :=
  hilbertRestrict Function.Embedding.inl

/-- The second coordinate projection from a disjoint Hilbert sum. -/
noncomputable def hilbertRight : ℓ²(I ⊕ J, ℝ) →L[ℝ] ℓ²(J, ℝ) :=
  hilbertRestrict Function.Embedding.inr

@[simp] theorem hilbertLeft_apply (z : ℓ²(I ⊕ J, ℝ)) (i : I) :
    hilbertLeft z i = z (.inl i) := rfl

@[simp] theorem hilbertRight_apply (z : ℓ²(I ⊕ J, ℝ)) (j : J) :
    hilbertRight z j = z (.inr j) := rfl

/-- The coordinate decomposition as a continuous linear equivalence. -/
noncomputable def hilbertJoin : (ℓ²(I, ℝ) × ℓ²(J, ℝ)) ≃L[ℝ] ℓ²(I ⊕ J, ℝ) where
  toFun := hilbertJoinCLM
  invFun := fun z => (hilbertLeft z, hilbertRight z)
  map_add' := hilbertJoinCLM.map_add
  map_smul' := hilbertJoinCLM.map_smul
  left_inv := by intro p; apply Prod.ext <;> ext i <;> rfl
  right_inv := by intro z; ext (i | j) <;> rfl
  continuous_toFun := hilbertJoinCLM.continuous
  continuous_invFun := hilbertLeft.continuous.prodMk hilbertRight.continuous

@[simp] theorem hilbertJoin_apply (p : ℓ²(I, ℝ) × ℓ²(J, ℝ)) :
    hilbertJoin p = hilbertJoinVector p.1 p.2 := rfl

@[simp] theorem hilbertLeft_join (p : ℓ²(I, ℝ) × ℓ²(J, ℝ)) :
    hilbertLeft (hilbertJoin p) = p.1 := by ext i; rfl

@[simp] theorem hilbertRight_join (p : ℓ²(I, ℝ) × ℓ²(J, ℝ)) :
    hilbertRight (hilbertJoin p) = p.2 := by ext j; rfl

@[simp] theorem hilbertJoin_left_right (z : ℓ²(I ⊕ J, ℝ)) :
    hilbertJoin (hilbertLeft z, hilbertRight z) = z := hilbertJoin.apply_symm_apply z

/-- A finite-coordinate functional splits into the two disjoint sets of coordinates. -/
theorem hilbertFinsuppFunctional_sumElim (a : I →₀ ℝ) (b : J →₀ ℝ)
    (z : ℓ²(I ⊕ J, ℝ)) :
    hilbertFinsuppFunctional (a.sumElim b) z =
      hilbertFinsuppFunctional a (hilbertLeft z) +
        hilbertFinsuppFunctional b (hilbertRight z) := by
  classical
  simp only [hilbertFinsuppFunctional_apply, Finsupp.sumElim_support, Finset.sum_disjSum]
  rfl

@[simp] theorem hilbertFinsuppFunctional_sumElim_left (a : I →₀ ℝ)
    (z : ℓ²(I ⊕ J, ℝ)) :
    hilbertFinsuppFunctional (a.sumElim (0 : J →₀ ℝ)) z =
      hilbertFinsuppFunctional a (hilbertLeft z) := by
  rw [hilbertFinsuppFunctional_sumElim]
  simp [hilbertFinsuppFunctional]

@[simp] theorem hilbertFinsuppFunctional_sumElim_right (b : J →₀ ℝ)
    (z : ℓ²(I ⊕ J, ℝ)) :
    hilbertFinsuppFunctional ((0 : I →₀ ℝ).sumElim b) z =
      hilbertFinsuppFunctional b (hilbertRight z) := by
  rw [hilbertFinsuppFunctional_sumElim]
  simp [hilbertFinsuppFunctional]

end NoUniversalFSigma.Proof
