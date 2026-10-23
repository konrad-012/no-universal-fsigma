module

public import NoUniversalFSigma.Hilbert

@[expose] public section

/-! # Coordinate operators and elementary Hilbert tensors

The Hilbert tensor product needed here is represented concretely as `ℓ²(I × J, ℝ)`.
The elementary tensor has coordinates `x i * y j`; rows and columns are bounded coordinate
restrictions.  None of these constructions requires countability of the coordinate sets.
-/

open Set Filter
open scoped lp ENNReal

namespace NoUniversalFSigma.Proof

attribute [local instance] Classical.propDecidable

/-- Square summability of the coordinates of a real Hilbert vector. -/
lemma hilbert_summable_sq {I : Type*} (x : ℓ²(I, ℝ)) : Summable fun i => ‖x i‖ ^ 2 := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The norm squared is the sum of the coordinate norm squares. -/
lemma hilbert_norm_sq {I : Type*} (x : ℓ²(I, ℝ)) : ‖x‖ ^ 2 = ∑' i, ‖x i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

/-- Restriction along an injective map of coordinate sets, as a bounded linear operator. -/
noncomputable def hilbertRestrict {I J : Type*} (e : I ↪ J) : ℓ²(J, ℝ) →L[ℝ] ℓ²(I, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => x (e i), memℓp_gen
        (((lp.memℓp x).summable (by norm_num)).comp_injective e.injective)⟩
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }
    1 (by
      intro x
      rw [one_mul]
      apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg x)
      intro s
      simpa using lp.sum_rpow_le_norm_rpow
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x (s.map e))

@[simp]
lemma hilbertRestrict_apply {I J : Type*} (e : I ↪ J) (x : ℓ²(J, ℝ)) (i : I) :
    hilbertRestrict e x i = x (e i) := rfl

lemma norm_hilbertRestrict_le {I J : Type*} (e : I ↪ J) (x : ℓ²(J, ℝ)) :
    ‖hilbertRestrict e x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg x)
  intro s
  simpa using lp.sum_rpow_le_norm_rpow
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x (s.map e)

/-- The row with first coordinate `i`. -/
noncomputable def hilbertRow {I J : Type*} (i : I) : ℓ²(I × J, ℝ) →L[ℝ] ℓ²(J, ℝ) :=
  hilbertRestrict ⟨fun j => (i, j), fun _ _ h => (Prod.mk.inj h).2⟩

/-- The column with second coordinate `j`. -/
noncomputable def hilbertColumn {I J : Type*} (j : J) : ℓ²(I × J, ℝ) →L[ℝ] ℓ²(I, ℝ) :=
  hilbertRestrict ⟨fun i => (i, j), fun _ _ h => (Prod.mk.inj h).1⟩

@[simp]
lemma hilbertRow_apply {I J : Type*} (i : I) (z : ℓ²(I × J, ℝ)) (j : J) :
    hilbertRow i z j = z (i, j) := rfl

@[simp]
lemma hilbertColumn_apply {I J : Type*} (j : J) (z : ℓ²(I × J, ℝ)) (i : I) :
    hilbertColumn j z i = z (i, j) := rfl

lemma norm_hilbertRow_le {I J : Type*} (i : I) (z : ℓ²(I × J, ℝ)) : ‖hilbertRow i z‖ ≤ ‖z‖ :=
  norm_hilbertRestrict_le _ _

lemma norm_hilbertColumn_le {I J : Type*} (j : J) (z : ℓ²(I × J, ℝ)) :
    ‖hilbertColumn j z‖ ≤ ‖z‖ := norm_hilbertRestrict_le _ _

/-- Products of two square-summable coordinate families are square summable on the product. -/
lemma memℓp_hilbertTensor {I J : Type*} (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    Memℓp (fun p : I × J => x p.1 * y p.2) 2 := by
  apply memℓp_gen
  have h := (hilbert_summable_sq x).mul_of_nonneg (hilbert_summable_sq y)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow] using h

/-- The elementary tensor, represented by its products of coordinates. -/
noncomputable def hilbertTensor {I J : Type*} (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) : ℓ²(I × J, ℝ) :=
  ⟨fun p => x p.1 * y p.2, memℓp_hilbertTensor x y⟩

@[simp]
lemma hilbertTensor_apply {I J : Type*} (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) (p : I × J) :
    hilbertTensor x y p = x p.1 * y p.2 := rfl

/-- The norm of an elementary tensor is the product of the two norms. -/
lemma norm_hilbertTensor {I J : Type*} (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    ‖hilbertTensor x y‖ = ‖x‖ * ‖y‖ := by
  have hs := (hilbert_summable_sq x).mul_of_nonneg (hilbert_summable_sq y)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have heq : ‖hilbertTensor x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
    rw [hilbert_norm_sq]
    simp only [hilbertTensor_apply, norm_mul, mul_pow]
    rw [← (hilbert_summable_sq x).tsum_mul_tsum (hilbert_summable_sq y) hs,
      ← hilbert_norm_sq x, ← hilbert_norm_sq y]
  nlinarith [norm_nonneg (hilbertTensor x y), norm_nonneg x, norm_nonneg y,
    mul_nonneg (norm_nonneg x) (norm_nonneg y)]

@[simp]
lemma hilbertTensor_add_left {I J : Type*} (x x' : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertTensor (x + x') y = hilbertTensor x y + hilbertTensor x' y := by
  ext p
  change (x p.1 + x' p.1) * y p.2 = x p.1 * y p.2 + x' p.1 * y p.2
  ring

@[simp]
lemma hilbertTensor_add_right {I J : Type*} (x : ℓ²(I, ℝ)) (y y' : ℓ²(J, ℝ)) :
    hilbertTensor x (y + y') = hilbertTensor x y + hilbertTensor x y' := by
  ext p
  change x p.1 * (y p.2 + y' p.2) = x p.1 * y p.2 + x p.1 * y' p.2
  ring

@[simp]
lemma hilbertTensor_smul_left {I J : Type*} (r : ℝ) (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertTensor (r • x) y = r • hilbertTensor x y := by
  ext p
  change (r * x p.1) * y p.2 = r * (x p.1 * y p.2)
  ring

@[simp]
lemma hilbertTensor_smul_right {I J : Type*} (r : ℝ) (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertTensor x (r • y) = r • hilbertTensor x y := by
  ext p
  change x p.1 * (r * y p.2) = r * (x p.1 * y p.2)
  ring

/-- The elementary tensor as a bilinear map. -/
noncomputable def hilbertTensorLinear {I J : Type*} :
    ℓ²(I, ℝ) →ₗ[ℝ] ℓ²(J, ℝ) →ₗ[ℝ] ℓ²(I × J, ℝ) where
  toFun x :=
    { toFun := hilbertTensor x
      map_add' := hilbertTensor_add_right x
      map_smul' := fun r y => hilbertTensor_smul_right r x y }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    exact hilbertTensor_add_left x x' y
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    exact hilbertTensor_smul_left r x y

/-- The elementary tensor as a continuous bilinear map. -/
noncomputable def hilbertTensorCLM {I J : Type*} :
    ℓ²(I, ℝ) →L[ℝ] ℓ²(J, ℝ) →L[ℝ] ℓ²(I × J, ℝ) :=
  hilbertTensorLinear.mkContinuous₂ 1 (fun x y => by
    change ‖hilbertTensor x y‖ ≤ 1 * ‖x‖ * ‖y‖
    rw [one_mul, norm_hilbertTensor])

@[simp]
lemma hilbertTensorCLM_apply {I J : Type*} (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertTensorCLM x y = hilbertTensor x y := rfl

/-- Joint norm continuity of the elementary tensor map. -/
lemma continuous_hilbertTensor {I J : Type*} :
    Continuous fun p : ℓ²(I, ℝ) × ℓ²(J, ℝ) => hilbertTensor p.1 p.2 :=
  hilbertTensorCLM.continuous₂

@[simp]
lemma hilbertRow_tensor {I J : Type*} (i : I) (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertRow i (hilbertTensor x y) = x i • y := by
  ext j
  rfl

@[simp]
lemma hilbertColumn_tensor {I J : Type*} (j : J) (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertColumn j (hilbertTensor x y) = y j • x := by
  ext i
  change x i * y j = y j * x i
  ring

/-- Contraction in the first tensor coordinate by a finitely supported functional. -/
noncomputable def hilbertContractLeft {I J : Type*} (a : I →₀ ℝ) :
    ℓ²(I × J, ℝ) →L[ℝ] ℓ²(J, ℝ) :=
  ∑ i ∈ a.support, a i • hilbertRow i

/-- Contraction in the second tensor coordinate by a finitely supported functional. -/
noncomputable def hilbertContractRight {I J : Type*} (b : J →₀ ℝ) :
    ℓ²(I × J, ℝ) →L[ℝ] ℓ²(I, ℝ) :=
  ∑ j ∈ b.support, b j • hilbertColumn j

@[simp]
lemma hilbertContractLeft_apply {I J : Type*} (a : I →₀ ℝ) (z : ℓ²(I × J, ℝ)) (j : J) :
    hilbertContractLeft a z j = ∑ i ∈ a.support, a i * z (i, j) := by
  unfold hilbertContractLeft
  rw [sum_apply]
  change (∑ i ∈ a.support, a i • hilbertRow i z) j = _
  rw [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

@[simp]
lemma hilbertContractRight_apply {I J : Type*} (b : J →₀ ℝ) (z : ℓ²(I × J, ℝ)) (i : I) :
    hilbertContractRight b z i = ∑ j ∈ b.support, b j * z (i, j) := by
  unfold hilbertContractRight
  rw [sum_apply]
  change (∑ j ∈ b.support, b j • hilbertColumn j z) i = _
  rw [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

@[simp]
lemma hilbertContractLeft_tensor {I J : Type*} (a : I →₀ ℝ) (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertContractLeft a (hilbertTensor x y) = hilbertFinsuppFunctional a x • y := by
  ext j
  rw [hilbertContractLeft_apply]
  change (∑ i ∈ a.support, a i * (x i * y j)) = hilbertFinsuppFunctional a x * y j
  rw [hilbertFinsuppFunctional_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp]
lemma hilbertContractRight_tensor {I J : Type*} (b : J →₀ ℝ) (x : ℓ²(I, ℝ)) (y : ℓ²(J, ℝ)) :
    hilbertContractRight b (hilbertTensor x y) = hilbertFinsuppFunctional b y • x := by
  ext i
  rw [hilbertContractRight_apply]
  change (∑ j ∈ b.support, b j * (x i * y j)) = hilbertFinsuppFunctional b y * x i
  rw [hilbertFinsuppFunctional_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end NoUniversalFSigma.Proof
